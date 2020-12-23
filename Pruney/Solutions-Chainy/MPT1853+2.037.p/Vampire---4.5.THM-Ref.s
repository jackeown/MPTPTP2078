%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:47 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  255 ( 557 expanded)
%              Number of leaves         :   56 ( 227 expanded)
%              Depth                    :   11
%              Number of atoms          :  823 (1634 expanded)
%              Number of equality atoms :   49 ( 104 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f110,f114,f134,f141,f146,f174,f184,f198,f202,f210,f216,f222,f245,f270,f301,f353,f354,f375,f482,f589,f693,f884,f896,f998,f1005,f1026,f1092,f1176,f1254,f1274,f1275,f1277,f1302,f1303,f1304])).

fof(f1304,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | r2_hidden(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1303,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1302,plain,
    ( ~ spl5_2
    | spl5_6
    | ~ spl5_14
    | ~ spl5_30
    | ~ spl5_59 ),
    inference(avatar_contradiction_clause,[],[f1301])).

fof(f1301,plain,
    ( $false
    | ~ spl5_2
    | spl5_6
    | ~ spl5_14
    | ~ spl5_30
    | ~ spl5_59 ),
    inference(subsumption_resolution,[],[f417,f689])).

fof(f689,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl5_59
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f417,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_2
    | spl5_6
    | ~ spl5_14
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f416,f147])).

fof(f147,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_6
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f416,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f415,f104])).

fof(f104,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f415,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_14
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f414,f183])).

fof(f183,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl5_14
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f414,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_30 ),
    inference(superposition,[],[f68,f352])).

fof(f352,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl5_30
  <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f1277,plain,
    ( k1_tarski(sK1) != u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_subset_1(k1_tarski(sK1),k1_tarski(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1275,plain,
    ( k1_tarski(sK1) != u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(k1_tarski(sK1),k1_tarski(sK1))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_tarski(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1274,plain,
    ( spl5_122
    | spl5_5
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_99
    | ~ spl5_105
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f1244,f1174,f1090,f1024,f243,f144,f132,f1272])).

fof(f1272,plain,
    ( spl5_122
  <=> k1_tarski(sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f132,plain,
    ( spl5_5
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f144,plain,
    ( spl5_8
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f243,plain,
    ( spl5_19
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1024,plain,
    ( spl5_99
  <=> m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f1090,plain,
    ( spl5_105
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f1174,plain,
    ( spl5_112
  <=> k1_tarski(sK1) = k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f1244,plain,
    ( k1_tarski(sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | spl5_5
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_99
    | ~ spl5_105
    | ~ spl5_112 ),
    inference(subsumption_resolution,[],[f1096,f1243])).

fof(f1243,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl5_5
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_99
    | ~ spl5_112 ),
    inference(subsumption_resolution,[],[f1242,f145])).

fof(f145,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f144])).

fof(f1242,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl5_5
    | ~ spl5_19
    | ~ spl5_99
    | ~ spl5_112 ),
    inference(subsumption_resolution,[],[f1241,f133])).

fof(f133,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1241,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_19
    | ~ spl5_99
    | ~ spl5_112 ),
    inference(subsumption_resolution,[],[f1240,f1025])).

fof(f1025,plain,
    ( m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_99 ),
    inference(avatar_component_clause,[],[f1024])).

fof(f1240,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_19
    | ~ spl5_112 ),
    inference(subsumption_resolution,[],[f1238,f244])).

fof(f244,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f243])).

fof(f1238,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_112 ),
    inference(superposition,[],[f90,f1175])).

fof(f1175,plain,
    ( k1_tarski(sK1) = k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1)
    | ~ spl5_112 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(f1096,plain,
    ( k1_tarski(sK1) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_105 ),
    inference(resolution,[],[f1091,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f1091,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))))
    | ~ spl5_105 ),
    inference(avatar_component_clause,[],[f1090])).

fof(f1254,plain,
    ( ~ spl5_118
    | spl5_5
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_99
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f1243,f1174,f1024,f243,f144,f132,f1252])).

fof(f1252,plain,
    ( spl5_118
  <=> v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f1176,plain,
    ( spl5_112
    | spl5_52
    | ~ spl5_99 ),
    inference(avatar_split_clause,[],[f1047,f1024,f629,f1174])).

fof(f629,plain,
    ( spl5_52
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1047,plain,
    ( k1_tarski(sK1) = k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1)
    | spl5_52
    | ~ spl5_99 ),
    inference(subsumption_resolution,[],[f1038,f1014])).

fof(f1014,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl5_52 ),
    inference(avatar_component_clause,[],[f629])).

fof(f1038,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | k1_tarski(sK1) = k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1)
    | ~ spl5_99 ),
    inference(resolution,[],[f1025,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f1092,plain,
    ( spl5_105
    | spl5_52
    | ~ spl5_99 ),
    inference(avatar_split_clause,[],[f1049,f1024,f629,f1090])).

fof(f1049,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))))
    | spl5_52
    | ~ spl5_99 ),
    inference(forward_demodulation,[],[f1048,f1047])).

fof(f1048,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))))
    | spl5_52
    | ~ spl5_99 ),
    inference(subsumption_resolution,[],[f1039,f1014])).

fof(f1039,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | m1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))))
    | ~ spl5_99 ),
    inference(resolution,[],[f1025,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f1026,plain,
    ( spl5_99
    | ~ spl5_97 ),
    inference(avatar_split_clause,[],[f1010,f996,f1024])).

fof(f996,plain,
    ( spl5_97
  <=> r2_hidden(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f1010,plain,
    ( m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_97 ),
    inference(subsumption_resolution,[],[f1009,f1008])).

fof(f1008,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_97 ),
    inference(resolution,[],[f997,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f997,plain,
    ( r2_hidden(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f996])).

fof(f1009,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_97 ),
    inference(resolution,[],[f997,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f1005,plain,
    ( spl5_5
    | ~ spl5_19
    | ~ spl5_52 ),
    inference(avatar_contradiction_clause,[],[f1004])).

fof(f1004,plain,
    ( $false
    | spl5_5
    | ~ spl5_19
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f1003,f133])).

fof(f1003,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_19
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f999,f244])).

fof(f999,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_52 ),
    inference(resolution,[],[f630,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f630,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f629])).

fof(f998,plain,
    ( spl5_52
    | spl5_97
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f916,f894,f996,f629])).

fof(f894,plain,
    ( spl5_87
  <=> sK1 = sK4(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f916,plain,
    ( r2_hidden(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_87 ),
    inference(superposition,[],[f87,f895])).

fof(f895,plain,
    ( sK1 = sK4(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f894])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f896,plain,
    ( spl5_87
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f886,f882,f894])).

fof(f882,plain,
    ( spl5_86
  <=> r2_hidden(sK4(u1_struct_0(k1_tex_2(sK0,sK1))),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f886,plain,
    ( sK1 = sK4(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_86 ),
    inference(resolution,[],[f883,f95])).

fof(f95,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f883,plain,
    ( r2_hidden(sK4(u1_struct_0(k1_tex_2(sK0,sK1))),k1_tarski(sK1))
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f882])).

fof(f884,plain,
    ( spl5_52
    | spl5_86
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f658,f373,f299,f882,f629])).

fof(f299,plain,
    ( spl5_26
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f373,plain,
    ( spl5_32
  <=> u1_struct_0(sK0) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f658,plain,
    ( r2_hidden(sK4(u1_struct_0(k1_tex_2(sK0,sK1))),k1_tarski(sK1))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f656,f374])).

fof(f374,plain,
    ( u1_struct_0(sK0) = k1_tarski(sK1)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f373])).

fof(f656,plain,
    ( r2_hidden(sK4(u1_struct_0(k1_tex_2(sK0,sK1))),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl5_26 ),
    inference(resolution,[],[f306,f87])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(k1_tex_2(sK0,sK1)))
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl5_26 ),
    inference(resolution,[],[f300,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f300,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f299])).

fof(f693,plain,
    ( spl5_59
    | spl5_60
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f307,f299,f691,f688])).

fof(f691,plain,
    ( spl5_60
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f307,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_26 ),
    inference(resolution,[],[f300,f59])).

fof(f589,plain,
    ( spl5_48
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f472,f373,f299,f182,f136,f103,f587])).

fof(f587,plain,
    ( spl5_48
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f472,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_tarski(sK1))
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f361,f374])).

fof(f361,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f356,f137])).

fof(f137,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f356,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_2
    | ~ spl5_14
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f355,f104])).

fof(f355,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_14
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f305,f183])).

fof(f305,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_26 ),
    inference(resolution,[],[f300,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f482,plain,
    ( spl5_12
    | spl5_21
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f357,f208,f112,f252,f172])).

fof(f172,plain,
    ( spl5_12
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f252,plain,
    ( spl5_21
  <=> v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f112,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f208,plain,
    ( spl5_17
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f357,plain,
    ( v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f130,f209])).

fof(f209,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f208])).

fof(f130,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f121,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f121,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(f113,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f375,plain,
    ( spl5_32
    | ~ spl5_6
    | ~ spl5_16
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f363,f208,f200,f136,f373])).

fof(f200,plain,
    ( spl5_16
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f363,plain,
    ( u1_struct_0(sK0) = k1_tarski(sK1)
    | ~ spl5_6
    | ~ spl5_16
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f231,f360])).

fof(f360,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl5_6
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f257,f137])).

fof(f257,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f55,f209])).

fof(f55,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f231,plain,
    ( u1_struct_0(sK0) = k1_tarski(sK1)
    | v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(resolution,[],[f201,f59])).

fof(f201,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f200])).

fof(f354,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f353,plain,
    ( spl5_30
    | ~ spl5_2
    | ~ spl5_4
    | spl5_12
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f260,f208,f182,f172,f112,f103,f351])).

fof(f260,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_4
    | spl5_12
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f193,f258])).

fof(f258,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_4
    | spl5_12
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f257,f256])).

fof(f256,plain,
    ( v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl5_4
    | spl5_12
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f255,f209])).

fof(f255,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_4
    | spl5_12 ),
    inference(subsumption_resolution,[],[f130,f173])).

fof(f173,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f193,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f188,f104])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f183,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f301,plain,
    ( spl5_26
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f190,f182,f103,f299])).

fof(f190,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f186,f104])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(resolution,[],[f183,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f270,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_12
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f258,f208,f172,f112,f136])).

fof(f245,plain,
    ( spl5_19
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f238,f196,f243])).

fof(f196,plain,
    ( spl5_15
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f238,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_15 ),
    inference(resolution,[],[f197,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f197,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f196])).

fof(f222,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f220,f100])).

fof(f100,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f220,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f217,f109])).

fof(f109,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f217,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f215,f75])).

fof(f215,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f216,plain,
    ( spl5_10
    | spl5_13
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f120,f112,f176,f160])).

fof(f176,plain,
    ( spl5_13
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f120,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f210,plain,
    ( spl5_17
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f204,f176,f112,f208])).

fof(f204,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f122,f179])).

fof(f179,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_13 ),
    inference(resolution,[],[f177,f88])).

fof(f177,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f176])).

fof(f122,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f62])).

fof(f202,plain,
    ( spl5_16
    | ~ spl5_4
    | spl5_10 ),
    inference(avatar_split_clause,[],[f170,f160,f112,f200])).

fof(f170,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | spl5_10 ),
    inference(forward_demodulation,[],[f167,f168])).

fof(f168,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl5_4
    | spl5_10 ),
    inference(subsumption_resolution,[],[f122,f161])).

fof(f161,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f167,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | spl5_10 ),
    inference(subsumption_resolution,[],[f123,f161])).

fof(f123,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f61])).

fof(f198,plain,
    ( spl5_15
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f189,f182,f103,f196])).

fof(f189,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f185,f104])).

fof(f185,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl5_14 ),
    inference(resolution,[],[f183,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f184,plain,
    ( spl5_14
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f129,f112,f103,f99,f182])).

fof(f129,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f128,f100])).

fof(f128,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f118,f104])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f174,plain,
    ( ~ spl5_12
    | ~ spl5_4
    | ~ spl5_7
    | spl5_10 ),
    inference(avatar_split_clause,[],[f166,f160,f139,f112,f172])).

fof(f139,plain,
    ( spl5_7
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f166,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl5_4
    | ~ spl5_7
    | spl5_10 ),
    inference(subsumption_resolution,[],[f154,f161])).

fof(f154,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f150,f113])).

fof(f150,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f140,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f140,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f146,plain,
    ( spl5_8
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f127,f112,f103,f99,f144])).

fof(f127,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f126,f100])).

fof(f126,plain,
    ( v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f116,f104])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f141,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f54,f139,f136])).

fof(f54,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f134,plain,
    ( ~ spl5_5
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f125,f112,f103,f99,f132])).

fof(f125,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f124,f100])).

fof(f124,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f115,f104])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f56,f112])).

fof(f56,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f110,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f106,f103,f108])).

fof(f106,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f104,f91])).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f58,f103])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f57,f99])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (17206)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.47  % (17206)Refutation not found, incomplete strategy% (17206)------------------------------
% 0.21/0.47  % (17206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17206)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (17206)Memory used [KB]: 10618
% 0.21/0.47  % (17206)Time elapsed: 0.063 s
% 0.21/0.47  % (17206)------------------------------
% 0.21/0.47  % (17206)------------------------------
% 0.21/0.48  % (17214)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.48  % (17205)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (17195)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (17210)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (17199)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (17210)Refutation not found, incomplete strategy% (17210)------------------------------
% 0.21/0.51  % (17210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17210)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17210)Memory used [KB]: 10618
% 0.21/0.51  % (17210)Time elapsed: 0.111 s
% 0.21/0.51  % (17210)------------------------------
% 0.21/0.51  % (17210)------------------------------
% 0.21/0.52  % (17203)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (17194)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (17213)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (17204)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (17222)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (17208)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (17196)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (17215)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (17204)Refutation not found, incomplete strategy% (17204)------------------------------
% 0.21/0.52  % (17204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17204)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17204)Memory used [KB]: 10746
% 0.21/0.52  % (17204)Time elapsed: 0.118 s
% 0.21/0.52  % (17204)------------------------------
% 0.21/0.52  % (17204)------------------------------
% 0.21/0.52  % (17220)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (17222)Refutation not found, incomplete strategy% (17222)------------------------------
% 0.21/0.52  % (17222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17222)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17222)Memory used [KB]: 10746
% 0.21/0.52  % (17222)Time elapsed: 0.125 s
% 0.21/0.52  % (17222)------------------------------
% 0.21/0.52  % (17222)------------------------------
% 0.21/0.52  % (17198)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (17209)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (17219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (17216)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (17207)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (17212)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (17223)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (17223)Refutation not found, incomplete strategy% (17223)------------------------------
% 0.21/0.53  % (17223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17223)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17223)Memory used [KB]: 1663
% 0.21/0.53  % (17223)Time elapsed: 0.001 s
% 0.21/0.53  % (17223)------------------------------
% 0.21/0.53  % (17223)------------------------------
% 0.21/0.53  % (17200)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (17197)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (17211)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (17218)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (17202)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (17201)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (17217)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (17221)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.79/0.59  % (17224)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.79/0.61  % (17220)Refutation found. Thanks to Tanya!
% 1.79/0.61  % SZS status Theorem for theBenchmark
% 1.79/0.61  % SZS output start Proof for theBenchmark
% 1.79/0.61  fof(f1305,plain,(
% 1.79/0.61    $false),
% 1.79/0.61    inference(avatar_sat_refutation,[],[f101,f105,f110,f114,f134,f141,f146,f174,f184,f198,f202,f210,f216,f222,f245,f270,f301,f353,f354,f375,f482,f589,f693,f884,f896,f998,f1005,f1026,f1092,f1176,f1254,f1274,f1275,f1277,f1302,f1303,f1304])).
% 1.79/0.61  fof(f1304,plain,(
% 1.79/0.61    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | r2_hidden(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) | ~r2_hidden(sK1,u1_struct_0(sK0))),
% 1.79/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.79/0.61  fof(f1303,plain,(
% 1.79/0.61    k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1) | u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.79/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.79/0.61  fof(f1302,plain,(
% 1.79/0.61    ~spl5_2 | spl5_6 | ~spl5_14 | ~spl5_30 | ~spl5_59),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f1301])).
% 1.79/0.61  fof(f1301,plain,(
% 1.79/0.61    $false | (~spl5_2 | spl5_6 | ~spl5_14 | ~spl5_30 | ~spl5_59)),
% 1.79/0.61    inference(subsumption_resolution,[],[f417,f689])).
% 1.79/0.61  fof(f689,plain,(
% 1.79/0.61    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl5_59),
% 1.79/0.61    inference(avatar_component_clause,[],[f688])).
% 1.79/0.61  fof(f688,plain,(
% 1.79/0.61    spl5_59 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 1.79/0.61  fof(f417,plain,(
% 1.79/0.61    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl5_2 | spl5_6 | ~spl5_14 | ~spl5_30)),
% 1.79/0.61    inference(subsumption_resolution,[],[f416,f147])).
% 1.79/0.61  fof(f147,plain,(
% 1.79/0.61    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl5_6),
% 1.79/0.61    inference(avatar_component_clause,[],[f136])).
% 1.79/0.61  fof(f136,plain,(
% 1.79/0.61    spl5_6 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.79/0.61  fof(f416,plain,(
% 1.79/0.61    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl5_2 | ~spl5_14 | ~spl5_30)),
% 1.79/0.61    inference(subsumption_resolution,[],[f415,f104])).
% 1.79/0.61  fof(f104,plain,(
% 1.79/0.61    l1_pre_topc(sK0) | ~spl5_2),
% 1.79/0.61    inference(avatar_component_clause,[],[f103])).
% 1.79/0.61  fof(f103,plain,(
% 1.79/0.61    spl5_2 <=> l1_pre_topc(sK0)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.79/0.61  fof(f415,plain,(
% 1.79/0.61    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl5_14 | ~spl5_30)),
% 1.79/0.61    inference(subsumption_resolution,[],[f414,f183])).
% 1.79/0.61  fof(f183,plain,(
% 1.79/0.61    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl5_14),
% 1.79/0.61    inference(avatar_component_clause,[],[f182])).
% 1.79/0.61  fof(f182,plain,(
% 1.79/0.61    spl5_14 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.79/0.61  fof(f414,plain,(
% 1.79/0.61    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl5_30),
% 1.79/0.61    inference(superposition,[],[f68,f352])).
% 1.79/0.61  fof(f352,plain,(
% 1.79/0.61    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~spl5_30),
% 1.79/0.61    inference(avatar_component_clause,[],[f351])).
% 1.79/0.61  fof(f351,plain,(
% 1.79/0.61    spl5_30 <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.79/0.61  fof(f68,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f39])).
% 1.79/0.61  fof(f39,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.79/0.61    inference(flattening,[],[f38])).
% 1.79/0.61  fof(f38,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.79/0.61    inference(ennf_transformation,[],[f16])).
% 1.79/0.61  fof(f16,axiom,(
% 1.79/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 1.79/0.61  fof(f1277,plain,(
% 1.79/0.61    k1_tarski(sK1) != u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_subset_1(k1_tarski(sK1),k1_tarski(sK1))),
% 1.79/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.79/0.61  fof(f1275,plain,(
% 1.79/0.61    k1_tarski(sK1) != u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(k1_tarski(sK1),k1_tarski(sK1)) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_tarski(sK1))),
% 1.79/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.79/0.61  fof(f1274,plain,(
% 1.79/0.61    spl5_122 | spl5_5 | ~spl5_8 | ~spl5_19 | ~spl5_99 | ~spl5_105 | ~spl5_112),
% 1.79/0.61    inference(avatar_split_clause,[],[f1244,f1174,f1090,f1024,f243,f144,f132,f1272])).
% 1.79/0.61  fof(f1272,plain,(
% 1.79/0.61    spl5_122 <=> k1_tarski(sK1) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).
% 1.79/0.61  fof(f132,plain,(
% 1.79/0.61    spl5_5 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.79/0.61  fof(f144,plain,(
% 1.79/0.61    spl5_8 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.79/0.61  fof(f243,plain,(
% 1.79/0.61    spl5_19 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.79/0.61  fof(f1024,plain,(
% 1.79/0.61    spl5_99 <=> m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).
% 1.79/0.61  fof(f1090,plain,(
% 1.79/0.61    spl5_105 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).
% 1.79/0.61  fof(f1174,plain,(
% 1.79/0.61    spl5_112 <=> k1_tarski(sK1) = k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).
% 1.79/0.61  fof(f1244,plain,(
% 1.79/0.61    k1_tarski(sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | (spl5_5 | ~spl5_8 | ~spl5_19 | ~spl5_99 | ~spl5_105 | ~spl5_112)),
% 1.79/0.61    inference(subsumption_resolution,[],[f1096,f1243])).
% 1.79/0.61  fof(f1243,plain,(
% 1.79/0.61    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | (spl5_5 | ~spl5_8 | ~spl5_19 | ~spl5_99 | ~spl5_112)),
% 1.79/0.61    inference(subsumption_resolution,[],[f1242,f145])).
% 1.79/0.61  fof(f145,plain,(
% 1.79/0.61    v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_8),
% 1.79/0.61    inference(avatar_component_clause,[],[f144])).
% 1.79/0.61  fof(f1242,plain,(
% 1.79/0.61    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | (spl5_5 | ~spl5_19 | ~spl5_99 | ~spl5_112)),
% 1.79/0.61    inference(subsumption_resolution,[],[f1241,f133])).
% 1.79/0.61  fof(f133,plain,(
% 1.79/0.61    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl5_5),
% 1.79/0.61    inference(avatar_component_clause,[],[f132])).
% 1.79/0.61  fof(f1241,plain,(
% 1.79/0.61    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl5_19 | ~spl5_99 | ~spl5_112)),
% 1.79/0.61    inference(subsumption_resolution,[],[f1240,f1025])).
% 1.79/0.61  fof(f1025,plain,(
% 1.79/0.61    m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_99),
% 1.79/0.61    inference(avatar_component_clause,[],[f1024])).
% 1.79/0.61  fof(f1240,plain,(
% 1.79/0.61    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | ~m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl5_19 | ~spl5_112)),
% 1.79/0.61    inference(subsumption_resolution,[],[f1238,f244])).
% 1.79/0.61  fof(f244,plain,(
% 1.79/0.61    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_19),
% 1.79/0.61    inference(avatar_component_clause,[],[f243])).
% 1.79/0.62  fof(f1238,plain,(
% 1.79/0.62    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_112),
% 1.79/0.62    inference(superposition,[],[f90,f1175])).
% 1.79/0.62  fof(f1175,plain,(
% 1.79/0.62    k1_tarski(sK1) = k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1) | ~spl5_112),
% 1.79/0.62    inference(avatar_component_clause,[],[f1174])).
% 1.79/0.62  fof(f90,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f52])).
% 1.79/0.62  fof(f52,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.79/0.62    inference(flattening,[],[f51])).
% 1.79/0.62  fof(f51,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f22])).
% 1.79/0.62  fof(f22,axiom,(
% 1.79/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).
% 1.79/0.62  fof(f1096,plain,(
% 1.79/0.62    k1_tarski(sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_105),
% 1.79/0.62    inference(resolution,[],[f1091,f59])).
% 1.79/0.62  fof(f59,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f29])).
% 1.79/0.62  fof(f29,plain,(
% 1.79/0.62    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f17])).
% 1.79/0.62  fof(f17,axiom,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.79/0.62  fof(f1091,plain,(
% 1.79/0.62    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))) | ~spl5_105),
% 1.79/0.62    inference(avatar_component_clause,[],[f1090])).
% 1.79/0.62  fof(f1254,plain,(
% 1.79/0.62    ~spl5_118 | spl5_5 | ~spl5_8 | ~spl5_19 | ~spl5_99 | ~spl5_112),
% 1.79/0.62    inference(avatar_split_clause,[],[f1243,f1174,f1024,f243,f144,f132,f1252])).
% 1.79/0.62  fof(f1252,plain,(
% 1.79/0.62    spl5_118 <=> v1_subset_1(k1_tarski(sK1),u1_struct_0(k1_tex_2(sK0,sK1)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).
% 1.79/0.62  fof(f1176,plain,(
% 1.79/0.62    spl5_112 | spl5_52 | ~spl5_99),
% 1.79/0.62    inference(avatar_split_clause,[],[f1047,f1024,f629,f1174])).
% 1.79/0.62  fof(f629,plain,(
% 1.79/0.62    spl5_52 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 1.79/0.62  fof(f1047,plain,(
% 1.79/0.62    k1_tarski(sK1) = k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1) | (spl5_52 | ~spl5_99)),
% 1.79/0.62    inference(subsumption_resolution,[],[f1038,f1014])).
% 1.79/0.62  fof(f1014,plain,(
% 1.79/0.62    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | spl5_52),
% 1.79/0.62    inference(avatar_component_clause,[],[f629])).
% 1.79/0.62  fof(f1038,plain,(
% 1.79/0.62    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | k1_tarski(sK1) = k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1) | ~spl5_99),
% 1.79/0.62    inference(resolution,[],[f1025,f62])).
% 1.79/0.62  fof(f62,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f33])).
% 1.79/0.62  fof(f33,plain,(
% 1.79/0.62    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.79/0.62    inference(flattening,[],[f32])).
% 1.79/0.62  fof(f32,plain,(
% 1.79/0.62    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f14])).
% 1.79/0.62  fof(f14,axiom,(
% 1.79/0.62    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.79/0.62  fof(f1092,plain,(
% 1.79/0.62    spl5_105 | spl5_52 | ~spl5_99),
% 1.79/0.62    inference(avatar_split_clause,[],[f1049,f1024,f629,f1090])).
% 1.79/0.62  fof(f1049,plain,(
% 1.79/0.62    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))) | (spl5_52 | ~spl5_99)),
% 1.79/0.62    inference(forward_demodulation,[],[f1048,f1047])).
% 1.79/0.62  fof(f1048,plain,(
% 1.79/0.62    m1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))) | (spl5_52 | ~spl5_99)),
% 1.79/0.62    inference(subsumption_resolution,[],[f1039,f1014])).
% 1.79/0.62  fof(f1039,plain,(
% 1.79/0.62    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | m1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(sK0,sK1)),sK1),k1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))) | ~spl5_99),
% 1.79/0.62    inference(resolution,[],[f1025,f61])).
% 1.79/0.62  fof(f61,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f31])).
% 1.79/0.62  fof(f31,plain,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.79/0.62    inference(flattening,[],[f30])).
% 1.79/0.62  fof(f30,plain,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f13])).
% 1.79/0.62  fof(f13,axiom,(
% 1.79/0.62    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.79/0.62  fof(f1026,plain,(
% 1.79/0.62    spl5_99 | ~spl5_97),
% 1.79/0.62    inference(avatar_split_clause,[],[f1010,f996,f1024])).
% 1.79/0.62  fof(f996,plain,(
% 1.79/0.62    spl5_97 <=> r2_hidden(sK1,u1_struct_0(k1_tex_2(sK0,sK1)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 1.79/0.62  fof(f1010,plain,(
% 1.79/0.62    m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_97),
% 1.79/0.62    inference(subsumption_resolution,[],[f1009,f1008])).
% 1.79/0.62  fof(f1008,plain,(
% 1.79/0.62    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_97),
% 1.79/0.62    inference(resolution,[],[f997,f88])).
% 1.79/0.62  fof(f88,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f1])).
% 1.79/0.62  fof(f1,axiom,(
% 1.79/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.79/0.62  fof(f997,plain,(
% 1.79/0.62    r2_hidden(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_97),
% 1.79/0.62    inference(avatar_component_clause,[],[f996])).
% 1.79/0.62  fof(f1009,plain,(
% 1.79/0.62    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | m1_subset_1(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_97),
% 1.79/0.62    inference(resolution,[],[f997,f85])).
% 1.79/0.62  fof(f85,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f49])).
% 1.79/0.62  fof(f49,plain,(
% 1.79/0.62    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f5])).
% 1.79/0.62  fof(f5,axiom,(
% 1.79/0.62    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.79/0.62  fof(f1005,plain,(
% 1.79/0.62    spl5_5 | ~spl5_19 | ~spl5_52),
% 1.79/0.62    inference(avatar_contradiction_clause,[],[f1004])).
% 1.79/0.62  fof(f1004,plain,(
% 1.79/0.62    $false | (spl5_5 | ~spl5_19 | ~spl5_52)),
% 1.79/0.62    inference(subsumption_resolution,[],[f1003,f133])).
% 1.79/0.62  fof(f1003,plain,(
% 1.79/0.62    v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl5_19 | ~spl5_52)),
% 1.79/0.62    inference(subsumption_resolution,[],[f999,f244])).
% 1.79/0.62  fof(f999,plain,(
% 1.79/0.62    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_52),
% 1.79/0.62    inference(resolution,[],[f630,f75])).
% 1.79/0.62  fof(f75,plain,(
% 1.79/0.62    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f47])).
% 1.79/0.62  fof(f47,plain,(
% 1.79/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.79/0.62    inference(flattening,[],[f46])).
% 1.79/0.62  fof(f46,plain,(
% 1.79/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f12])).
% 1.79/0.62  fof(f12,axiom,(
% 1.79/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.79/0.62  fof(f630,plain,(
% 1.79/0.62    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_52),
% 1.79/0.62    inference(avatar_component_clause,[],[f629])).
% 1.79/0.62  fof(f998,plain,(
% 1.79/0.62    spl5_52 | spl5_97 | ~spl5_87),
% 1.79/0.62    inference(avatar_split_clause,[],[f916,f894,f996,f629])).
% 1.79/0.62  fof(f894,plain,(
% 1.79/0.62    spl5_87 <=> sK1 = sK4(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 1.79/0.62  fof(f916,plain,(
% 1.79/0.62    r2_hidden(sK1,u1_struct_0(k1_tex_2(sK0,sK1))) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_87),
% 1.79/0.62    inference(superposition,[],[f87,f895])).
% 1.79/0.62  fof(f895,plain,(
% 1.79/0.62    sK1 = sK4(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_87),
% 1.79/0.62    inference(avatar_component_clause,[],[f894])).
% 1.79/0.62  fof(f87,plain,(
% 1.79/0.62    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f1])).
% 1.79/0.62  fof(f896,plain,(
% 1.79/0.62    spl5_87 | ~spl5_86),
% 1.79/0.62    inference(avatar_split_clause,[],[f886,f882,f894])).
% 1.79/0.62  fof(f882,plain,(
% 1.79/0.62    spl5_86 <=> r2_hidden(sK4(u1_struct_0(k1_tex_2(sK0,sK1))),k1_tarski(sK1))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 1.79/0.62  fof(f886,plain,(
% 1.79/0.62    sK1 = sK4(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_86),
% 1.79/0.62    inference(resolution,[],[f883,f95])).
% 1.79/0.62  fof(f95,plain,(
% 1.79/0.62    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.79/0.62    inference(equality_resolution,[],[f77])).
% 1.79/0.62  fof(f77,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.79/0.62    inference(cnf_transformation,[],[f2])).
% 1.79/0.62  fof(f2,axiom,(
% 1.79/0.62    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.79/0.62  fof(f883,plain,(
% 1.79/0.62    r2_hidden(sK4(u1_struct_0(k1_tex_2(sK0,sK1))),k1_tarski(sK1)) | ~spl5_86),
% 1.79/0.62    inference(avatar_component_clause,[],[f882])).
% 1.79/0.62  fof(f884,plain,(
% 1.79/0.62    spl5_52 | spl5_86 | ~spl5_26 | ~spl5_32),
% 1.79/0.62    inference(avatar_split_clause,[],[f658,f373,f299,f882,f629])).
% 1.79/0.62  fof(f299,plain,(
% 1.79/0.62    spl5_26 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.79/0.62  fof(f373,plain,(
% 1.79/0.62    spl5_32 <=> u1_struct_0(sK0) = k1_tarski(sK1)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.79/0.62  fof(f658,plain,(
% 1.79/0.62    r2_hidden(sK4(u1_struct_0(k1_tex_2(sK0,sK1))),k1_tarski(sK1)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl5_26 | ~spl5_32)),
% 1.79/0.62    inference(forward_demodulation,[],[f656,f374])).
% 1.79/0.62  fof(f374,plain,(
% 1.79/0.62    u1_struct_0(sK0) = k1_tarski(sK1) | ~spl5_32),
% 1.79/0.62    inference(avatar_component_clause,[],[f373])).
% 1.79/0.62  fof(f656,plain,(
% 1.79/0.62    r2_hidden(sK4(u1_struct_0(k1_tex_2(sK0,sK1))),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl5_26),
% 1.79/0.62    inference(resolution,[],[f306,f87])).
% 1.79/0.62  fof(f306,plain,(
% 1.79/0.62    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(k1_tex_2(sK0,sK1))) | r2_hidden(X0,u1_struct_0(sK0))) ) | ~spl5_26),
% 1.79/0.62    inference(resolution,[],[f300,f81])).
% 1.79/0.62  fof(f81,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f48])).
% 1.79/0.62  fof(f48,plain,(
% 1.79/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f8])).
% 1.79/0.62  fof(f8,axiom,(
% 1.79/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.79/0.62  fof(f300,plain,(
% 1.79/0.62    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_26),
% 1.79/0.62    inference(avatar_component_clause,[],[f299])).
% 1.79/0.62  fof(f693,plain,(
% 1.79/0.62    spl5_59 | spl5_60 | ~spl5_26),
% 1.79/0.62    inference(avatar_split_clause,[],[f307,f299,f691,f688])).
% 1.79/0.62  fof(f691,plain,(
% 1.79/0.62    spl5_60 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 1.79/0.62  fof(f307,plain,(
% 1.79/0.62    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl5_26),
% 1.79/0.62    inference(resolution,[],[f300,f59])).
% 1.79/0.62  fof(f589,plain,(
% 1.79/0.62    spl5_48 | ~spl5_2 | ~spl5_6 | ~spl5_14 | ~spl5_26 | ~spl5_32),
% 1.79/0.62    inference(avatar_split_clause,[],[f472,f373,f299,f182,f136,f103,f587])).
% 1.79/0.62  fof(f587,plain,(
% 1.79/0.62    spl5_48 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_tarski(sK1))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 1.79/0.62  fof(f472,plain,(
% 1.79/0.62    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_tarski(sK1)) | (~spl5_2 | ~spl5_6 | ~spl5_14 | ~spl5_26 | ~spl5_32)),
% 1.79/0.62    inference(forward_demodulation,[],[f361,f374])).
% 1.79/0.62  fof(f361,plain,(
% 1.79/0.62    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_6 | ~spl5_14 | ~spl5_26)),
% 1.79/0.62    inference(subsumption_resolution,[],[f356,f137])).
% 1.79/0.62  fof(f137,plain,(
% 1.79/0.62    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl5_6),
% 1.79/0.62    inference(avatar_component_clause,[],[f136])).
% 1.79/0.62  fof(f356,plain,(
% 1.79/0.62    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl5_2 | ~spl5_14 | ~spl5_26)),
% 1.79/0.62    inference(subsumption_resolution,[],[f355,f104])).
% 1.79/0.62  fof(f355,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl5_14 | ~spl5_26)),
% 1.79/0.62    inference(subsumption_resolution,[],[f305,f183])).
% 1.79/0.62  fof(f305,plain,(
% 1.79/0.62    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl5_26),
% 1.79/0.62    inference(resolution,[],[f300,f94])).
% 1.79/0.62  fof(f94,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 1.79/0.62    inference(equality_resolution,[],[f65])).
% 1.79/0.62  fof(f65,plain,(
% 1.79/0.62    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f39])).
% 1.79/0.62  fof(f482,plain,(
% 1.79/0.62    spl5_12 | spl5_21 | ~spl5_4 | ~spl5_17),
% 1.79/0.62    inference(avatar_split_clause,[],[f357,f208,f112,f252,f172])).
% 1.79/0.62  fof(f172,plain,(
% 1.79/0.62    spl5_12 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.79/0.62  fof(f252,plain,(
% 1.79/0.62    spl5_21 <=> v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.79/0.62  fof(f112,plain,(
% 1.79/0.62    spl5_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.79/0.62  fof(f208,plain,(
% 1.79/0.62    spl5_17 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.79/0.62  fof(f357,plain,(
% 1.79/0.62    v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | (~spl5_4 | ~spl5_17)),
% 1.79/0.62    inference(forward_demodulation,[],[f130,f209])).
% 1.79/0.62  fof(f209,plain,(
% 1.79/0.62    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl5_17),
% 1.79/0.62    inference(avatar_component_clause,[],[f208])).
% 1.79/0.62  fof(f130,plain,(
% 1.79/0.62    v1_zfmisc_1(u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_4),
% 1.79/0.62    inference(subsumption_resolution,[],[f121,f89])).
% 1.79/0.62  fof(f89,plain,(
% 1.79/0.62    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f50])).
% 1.79/0.62  fof(f50,plain,(
% 1.79/0.62    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f4])).
% 1.79/0.62  fof(f4,axiom,(
% 1.79/0.62    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 1.79/0.62  fof(f121,plain,(
% 1.79/0.62    v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_4),
% 1.79/0.62    inference(resolution,[],[f113,f63])).
% 1.79/0.62  fof(f63,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f35])).
% 1.79/0.62  fof(f35,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.79/0.62    inference(flattening,[],[f34])).
% 1.79/0.62  fof(f34,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f21])).
% 1.79/0.62  fof(f21,axiom,(
% 1.79/0.62    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).
% 1.79/0.62  fof(f113,plain,(
% 1.79/0.62    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 1.79/0.62    inference(avatar_component_clause,[],[f112])).
% 1.79/0.62  fof(f375,plain,(
% 1.79/0.62    spl5_32 | ~spl5_6 | ~spl5_16 | ~spl5_17),
% 1.79/0.62    inference(avatar_split_clause,[],[f363,f208,f200,f136,f373])).
% 1.79/0.62  fof(f200,plain,(
% 1.79/0.62    spl5_16 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.79/0.62  fof(f363,plain,(
% 1.79/0.62    u1_struct_0(sK0) = k1_tarski(sK1) | (~spl5_6 | ~spl5_16 | ~spl5_17)),
% 1.79/0.62    inference(subsumption_resolution,[],[f231,f360])).
% 1.79/0.62  fof(f360,plain,(
% 1.79/0.62    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | (~spl5_6 | ~spl5_17)),
% 1.79/0.62    inference(subsumption_resolution,[],[f257,f137])).
% 1.79/0.62  fof(f257,plain,(
% 1.79/0.62    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl5_17),
% 1.79/0.62    inference(forward_demodulation,[],[f55,f209])).
% 1.79/0.62  fof(f55,plain,(
% 1.79/0.62    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f28,plain,(
% 1.79/0.62    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/0.62    inference(flattening,[],[f27])).
% 1.79/0.62  fof(f27,plain,(
% 1.79/0.62    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f24])).
% 1.79/0.62  fof(f24,negated_conjecture,(
% 1.79/0.62    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.79/0.62    inference(negated_conjecture,[],[f23])).
% 1.79/0.62  fof(f23,conjecture,(
% 1.79/0.62    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 1.79/0.62  fof(f231,plain,(
% 1.79/0.62    u1_struct_0(sK0) = k1_tarski(sK1) | v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | ~spl5_16),
% 1.79/0.62    inference(resolution,[],[f201,f59])).
% 1.79/0.62  fof(f201,plain,(
% 1.79/0.62    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_16),
% 1.79/0.62    inference(avatar_component_clause,[],[f200])).
% 1.79/0.62  fof(f354,plain,(
% 1.79/0.62    k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))),
% 1.79/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.79/0.62  fof(f353,plain,(
% 1.79/0.62    spl5_30 | ~spl5_2 | ~spl5_4 | spl5_12 | ~spl5_14 | ~spl5_17),
% 1.79/0.62    inference(avatar_split_clause,[],[f260,f208,f182,f172,f112,f103,f351])).
% 1.79/0.62  fof(f260,plain,(
% 1.79/0.62    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | (~spl5_2 | ~spl5_4 | spl5_12 | ~spl5_14 | ~spl5_17)),
% 1.79/0.62    inference(subsumption_resolution,[],[f193,f258])).
% 1.79/0.62  fof(f258,plain,(
% 1.79/0.62    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl5_4 | spl5_12 | ~spl5_17)),
% 1.79/0.62    inference(subsumption_resolution,[],[f257,f256])).
% 1.79/0.62  fof(f256,plain,(
% 1.79/0.62    v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | (~spl5_4 | spl5_12 | ~spl5_17)),
% 1.79/0.62    inference(forward_demodulation,[],[f255,f209])).
% 1.79/0.62  fof(f255,plain,(
% 1.79/0.62    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl5_4 | spl5_12)),
% 1.79/0.62    inference(subsumption_resolution,[],[f130,f173])).
% 1.79/0.62  fof(f173,plain,(
% 1.79/0.62    ~v1_zfmisc_1(u1_struct_0(sK0)) | spl5_12),
% 1.79/0.62    inference(avatar_component_clause,[],[f172])).
% 1.79/0.62  fof(f193,plain,(
% 1.79/0.62    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl5_2 | ~spl5_14)),
% 1.79/0.62    inference(subsumption_resolution,[],[f188,f104])).
% 1.79/0.62  fof(f188,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl5_14),
% 1.79/0.62    inference(resolution,[],[f183,f67])).
% 1.79/0.62  fof(f67,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f39])).
% 1.79/0.62  fof(f301,plain,(
% 1.79/0.62    spl5_26 | ~spl5_2 | ~spl5_14),
% 1.79/0.62    inference(avatar_split_clause,[],[f190,f182,f103,f299])).
% 1.79/0.62  fof(f190,plain,(
% 1.79/0.62    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_2 | ~spl5_14)),
% 1.79/0.62    inference(subsumption_resolution,[],[f186,f104])).
% 1.79/0.62  fof(f186,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_14),
% 1.79/0.62    inference(resolution,[],[f183,f73])).
% 1.79/0.62  fof(f73,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f44])).
% 1.79/0.62  fof(f44,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f15])).
% 1.79/0.62  fof(f15,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.79/0.62  fof(f270,plain,(
% 1.79/0.62    ~spl5_6 | ~spl5_4 | spl5_12 | ~spl5_17),
% 1.79/0.62    inference(avatar_split_clause,[],[f258,f208,f172,f112,f136])).
% 1.79/0.62  fof(f245,plain,(
% 1.79/0.62    spl5_19 | ~spl5_15),
% 1.79/0.62    inference(avatar_split_clause,[],[f238,f196,f243])).
% 1.79/0.62  fof(f196,plain,(
% 1.79/0.62    spl5_15 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.79/0.62  fof(f238,plain,(
% 1.79/0.62    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_15),
% 1.79/0.62    inference(resolution,[],[f197,f91])).
% 1.79/0.62  fof(f91,plain,(
% 1.79/0.62    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f53])).
% 1.79/0.62  fof(f53,plain,(
% 1.79/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f10])).
% 1.79/0.62  fof(f10,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.79/0.62  fof(f197,plain,(
% 1.79/0.62    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl5_15),
% 1.79/0.62    inference(avatar_component_clause,[],[f196])).
% 1.79/0.62  fof(f222,plain,(
% 1.79/0.62    spl5_1 | ~spl5_3 | ~spl5_10),
% 1.79/0.62    inference(avatar_contradiction_clause,[],[f221])).
% 1.79/0.62  fof(f221,plain,(
% 1.79/0.62    $false | (spl5_1 | ~spl5_3 | ~spl5_10)),
% 1.79/0.62    inference(subsumption_resolution,[],[f220,f100])).
% 1.79/0.62  fof(f100,plain,(
% 1.79/0.62    ~v2_struct_0(sK0) | spl5_1),
% 1.79/0.62    inference(avatar_component_clause,[],[f99])).
% 1.79/0.62  fof(f99,plain,(
% 1.79/0.62    spl5_1 <=> v2_struct_0(sK0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.79/0.62  fof(f220,plain,(
% 1.79/0.62    v2_struct_0(sK0) | (~spl5_3 | ~spl5_10)),
% 1.79/0.62    inference(subsumption_resolution,[],[f217,f109])).
% 1.79/0.62  fof(f109,plain,(
% 1.79/0.62    l1_struct_0(sK0) | ~spl5_3),
% 1.79/0.62    inference(avatar_component_clause,[],[f108])).
% 1.79/0.62  fof(f108,plain,(
% 1.79/0.62    spl5_3 <=> l1_struct_0(sK0)),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.79/0.62  fof(f217,plain,(
% 1.79/0.62    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_10),
% 1.79/0.62    inference(resolution,[],[f215,f75])).
% 1.79/0.62  fof(f215,plain,(
% 1.79/0.62    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_10),
% 1.79/0.62    inference(avatar_component_clause,[],[f160])).
% 1.79/0.62  fof(f160,plain,(
% 1.79/0.62    spl5_10 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.79/0.62  fof(f216,plain,(
% 1.79/0.62    spl5_10 | spl5_13 | ~spl5_4),
% 1.79/0.62    inference(avatar_split_clause,[],[f120,f112,f176,f160])).
% 1.79/0.62  fof(f176,plain,(
% 1.79/0.62    spl5_13 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.79/0.62  fof(f120,plain,(
% 1.79/0.62    r2_hidden(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_4),
% 1.79/0.62    inference(resolution,[],[f113,f86])).
% 1.79/0.62  fof(f86,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f49])).
% 1.79/0.62  fof(f210,plain,(
% 1.79/0.62    spl5_17 | ~spl5_4 | ~spl5_13),
% 1.79/0.62    inference(avatar_split_clause,[],[f204,f176,f112,f208])).
% 1.79/0.62  fof(f204,plain,(
% 1.79/0.62    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | (~spl5_4 | ~spl5_13)),
% 1.79/0.62    inference(subsumption_resolution,[],[f122,f179])).
% 1.79/0.62  fof(f179,plain,(
% 1.79/0.62    ~v1_xboole_0(u1_struct_0(sK0)) | ~spl5_13),
% 1.79/0.62    inference(resolution,[],[f177,f88])).
% 1.79/0.62  fof(f177,plain,(
% 1.79/0.62    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl5_13),
% 1.79/0.62    inference(avatar_component_clause,[],[f176])).
% 1.79/0.62  fof(f122,plain,(
% 1.79/0.62    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl5_4),
% 1.79/0.62    inference(resolution,[],[f113,f62])).
% 1.79/0.62  fof(f202,plain,(
% 1.79/0.62    spl5_16 | ~spl5_4 | spl5_10),
% 1.79/0.62    inference(avatar_split_clause,[],[f170,f160,f112,f200])).
% 1.79/0.62  fof(f170,plain,(
% 1.79/0.62    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | spl5_10)),
% 1.79/0.62    inference(forward_demodulation,[],[f167,f168])).
% 1.79/0.62  fof(f168,plain,(
% 1.79/0.62    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | (~spl5_4 | spl5_10)),
% 1.79/0.62    inference(subsumption_resolution,[],[f122,f161])).
% 1.79/0.62  fof(f161,plain,(
% 1.79/0.62    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_10),
% 1.79/0.62    inference(avatar_component_clause,[],[f160])).
% 1.79/0.62  fof(f167,plain,(
% 1.79/0.62    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | spl5_10)),
% 1.79/0.62    inference(subsumption_resolution,[],[f123,f161])).
% 1.79/0.62  fof(f123,plain,(
% 1.79/0.62    v1_xboole_0(u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_4),
% 1.79/0.62    inference(resolution,[],[f113,f61])).
% 1.79/0.62  fof(f198,plain,(
% 1.79/0.62    spl5_15 | ~spl5_2 | ~spl5_14),
% 1.79/0.62    inference(avatar_split_clause,[],[f189,f182,f103,f196])).
% 1.79/0.62  fof(f189,plain,(
% 1.79/0.62    l1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl5_2 | ~spl5_14)),
% 1.79/0.62    inference(subsumption_resolution,[],[f185,f104])).
% 1.79/0.62  fof(f185,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl5_14),
% 1.79/0.62    inference(resolution,[],[f183,f74])).
% 1.79/0.62  fof(f74,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f45])).
% 1.79/0.62  fof(f45,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f11])).
% 1.79/0.62  fof(f11,axiom,(
% 1.79/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.79/0.62  fof(f184,plain,(
% 1.79/0.62    spl5_14 | spl5_1 | ~spl5_2 | ~spl5_4),
% 1.79/0.62    inference(avatar_split_clause,[],[f129,f112,f103,f99,f182])).
% 1.79/0.62  fof(f129,plain,(
% 1.79/0.62    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (spl5_1 | ~spl5_2 | ~spl5_4)),
% 1.79/0.62    inference(subsumption_resolution,[],[f128,f100])).
% 1.79/0.62  fof(f128,plain,(
% 1.79/0.62    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl5_2 | ~spl5_4)),
% 1.79/0.62    inference(subsumption_resolution,[],[f118,f104])).
% 1.79/0.62  fof(f118,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl5_4),
% 1.79/0.62    inference(resolution,[],[f113,f70])).
% 1.79/0.62  fof(f70,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f41])).
% 1.79/0.62  fof(f41,plain,(
% 1.79/0.62    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.62    inference(flattening,[],[f40])).
% 1.79/0.62  fof(f40,plain,(
% 1.79/0.62    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f26])).
% 1.79/0.62  fof(f26,plain,(
% 1.79/0.62    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.79/0.62    inference(pure_predicate_removal,[],[f18])).
% 1.79/0.62  fof(f18,axiom,(
% 1.79/0.62    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 1.79/0.62  fof(f174,plain,(
% 1.79/0.62    ~spl5_12 | ~spl5_4 | ~spl5_7 | spl5_10),
% 1.79/0.62    inference(avatar_split_clause,[],[f166,f160,f139,f112,f172])).
% 1.79/0.62  fof(f139,plain,(
% 1.79/0.62    spl5_7 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.79/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.79/0.62  fof(f166,plain,(
% 1.79/0.62    ~v1_zfmisc_1(u1_struct_0(sK0)) | (~spl5_4 | ~spl5_7 | spl5_10)),
% 1.79/0.62    inference(subsumption_resolution,[],[f154,f161])).
% 1.79/0.62  fof(f154,plain,(
% 1.79/0.62    v1_xboole_0(u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | (~spl5_4 | ~spl5_7)),
% 1.79/0.62    inference(subsumption_resolution,[],[f150,f113])).
% 1.79/0.62  fof(f150,plain,(
% 1.79/0.62    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | ~spl5_7),
% 1.79/0.62    inference(resolution,[],[f140,f64])).
% 1.79/0.62  fof(f64,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.79/0.62    inference(cnf_transformation,[],[f37])).
% 1.79/0.62  fof(f37,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 1.79/0.62    inference(flattening,[],[f36])).
% 1.79/0.62  fof(f36,plain,(
% 1.79/0.62    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 1.79/0.62    inference(ennf_transformation,[],[f20])).
% 1.79/0.62  fof(f20,axiom,(
% 1.79/0.62    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 1.79/0.62  fof(f140,plain,(
% 1.79/0.62    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_7),
% 1.79/0.62    inference(avatar_component_clause,[],[f139])).
% 1.79/0.62  fof(f146,plain,(
% 1.79/0.62    spl5_8 | spl5_1 | ~spl5_2 | ~spl5_4),
% 1.79/0.62    inference(avatar_split_clause,[],[f127,f112,f103,f99,f144])).
% 1.79/0.62  fof(f127,plain,(
% 1.79/0.62    v7_struct_0(k1_tex_2(sK0,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_4)),
% 1.79/0.62    inference(subsumption_resolution,[],[f126,f100])).
% 1.79/0.62  fof(f126,plain,(
% 1.79/0.62    v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl5_2 | ~spl5_4)),
% 1.79/0.62    inference(subsumption_resolution,[],[f116,f104])).
% 1.79/0.62  fof(f116,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_4),
% 1.79/0.62    inference(resolution,[],[f113,f72])).
% 1.79/0.62  fof(f72,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f43])).
% 1.79/0.62  fof(f43,plain,(
% 1.79/0.62    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.62    inference(flattening,[],[f42])).
% 1.79/0.62  fof(f42,plain,(
% 1.79/0.62    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.62    inference(ennf_transformation,[],[f25])).
% 1.79/0.62  fof(f25,plain,(
% 1.79/0.62    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.79/0.62    inference(pure_predicate_removal,[],[f19])).
% 1.79/0.62  fof(f19,axiom,(
% 1.79/0.62    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.79/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 1.79/0.62  fof(f141,plain,(
% 1.79/0.62    spl5_6 | spl5_7),
% 1.79/0.62    inference(avatar_split_clause,[],[f54,f139,f136])).
% 1.79/0.62  fof(f54,plain,(
% 1.79/0.62    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f134,plain,(
% 1.79/0.62    ~spl5_5 | spl5_1 | ~spl5_2 | ~spl5_4),
% 1.79/0.62    inference(avatar_split_clause,[],[f125,f112,f103,f99,f132])).
% 1.79/0.62  fof(f125,plain,(
% 1.79/0.62    ~v2_struct_0(k1_tex_2(sK0,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_4)),
% 1.79/0.62    inference(subsumption_resolution,[],[f124,f100])).
% 1.79/0.62  fof(f124,plain,(
% 1.79/0.62    v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl5_2 | ~spl5_4)),
% 1.79/0.62    inference(subsumption_resolution,[],[f115,f104])).
% 1.79/0.62  fof(f115,plain,(
% 1.79/0.62    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl5_4),
% 1.79/0.62    inference(resolution,[],[f113,f71])).
% 1.79/0.62  fof(f71,plain,(
% 1.79/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 1.79/0.62    inference(cnf_transformation,[],[f43])).
% 1.79/0.62  fof(f114,plain,(
% 1.79/0.62    spl5_4),
% 1.79/0.62    inference(avatar_split_clause,[],[f56,f112])).
% 1.79/0.62  fof(f56,plain,(
% 1.79/0.62    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f110,plain,(
% 1.79/0.62    spl5_3 | ~spl5_2),
% 1.79/0.62    inference(avatar_split_clause,[],[f106,f103,f108])).
% 1.79/0.62  fof(f106,plain,(
% 1.79/0.62    l1_struct_0(sK0) | ~spl5_2),
% 1.79/0.62    inference(resolution,[],[f104,f91])).
% 1.79/0.62  fof(f105,plain,(
% 1.79/0.62    spl5_2),
% 1.79/0.62    inference(avatar_split_clause,[],[f58,f103])).
% 1.79/0.62  fof(f58,plain,(
% 1.79/0.62    l1_pre_topc(sK0)),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  fof(f101,plain,(
% 1.79/0.62    ~spl5_1),
% 1.79/0.62    inference(avatar_split_clause,[],[f57,f99])).
% 1.79/0.62  fof(f57,plain,(
% 1.79/0.62    ~v2_struct_0(sK0)),
% 1.79/0.62    inference(cnf_transformation,[],[f28])).
% 1.79/0.62  % SZS output end Proof for theBenchmark
% 1.79/0.62  % (17220)------------------------------
% 1.79/0.62  % (17220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.62  % (17220)Termination reason: Refutation
% 1.79/0.62  
% 1.79/0.62  % (17220)Memory used [KB]: 7036
% 1.79/0.62  % (17220)Time elapsed: 0.211 s
% 1.79/0.62  % (17220)------------------------------
% 1.79/0.62  % (17220)------------------------------
% 2.04/0.62  % (17193)Success in time 0.266 s
%------------------------------------------------------------------------------
