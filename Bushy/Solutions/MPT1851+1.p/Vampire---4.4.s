%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t18_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:28 EDT 2019

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  455 ( 734 expanded)
%              Number of leaves         :  127 ( 328 expanded)
%              Depth                    :   10
%              Number of atoms          : 1175 (2110 expanded)
%              Number of equality atoms :   55 ( 145 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f359,f366,f373,f380,f387,f394,f401,f408,f415,f422,f429,f436,f443,f450,f457,f464,f471,f478,f485,f492,f499,f506,f513,f520,f527,f534,f541,f548,f555,f562,f569,f576,f583,f590,f597,f604,f611,f618,f625,f632,f639,f646,f653,f660,f667,f674,f681,f688,f695,f702,f709,f716,f723,f730,f737,f744,f751,f758,f765,f772,f779,f786,f793,f800,f807,f814,f821,f828,f835,f842,f860,f907,f921,f984,f1036,f1045,f1052,f1059,f1066,f1073,f1080,f1087,f1094,f1110,f1115,f1119,f1132,f1140,f1158,f1168,f1171,f1183,f1196,f1202,f1209,f1251])).

fof(f1251,plain,
    ( ~ spl21_0
    | spl21_5
    | ~ spl21_136
    | ~ spl21_150
    | ~ spl21_178
    | ~ spl21_182
    | ~ spl21_184 ),
    inference(avatar_contradiction_clause,[],[f1250])).

fof(f1250,plain,
    ( $false
    | ~ spl21_0
    | ~ spl21_5
    | ~ spl21_136
    | ~ spl21_150
    | ~ spl21_178
    | ~ spl21_182
    | ~ spl21_184 ),
    inference(subsumption_resolution,[],[f1249,f1244])).

fof(f1244,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK1)
    | ~ spl21_0
    | ~ spl21_5
    | ~ spl21_150
    | ~ spl21_178 ),
    inference(forward_demodulation,[],[f1243,f1035])).

fof(f1035,plain,
    ( u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl21_150 ),
    inference(avatar_component_clause,[],[f1034])).

fof(f1034,plain,
    ( spl21_150
  <=> u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_150])])).

fof(f1243,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl21_0
    | ~ spl21_5
    | ~ spl21_178 ),
    inference(subsumption_resolution,[],[f1242,f372])).

fof(f372,plain,
    ( ~ v2_tdlat_3(sK1)
    | ~ spl21_5 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl21_5
  <=> ~ v2_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_5])])).

fof(f1242,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | v2_tdlat_3(sK1)
    | ~ spl21_0
    | ~ spl21_178 ),
    inference(subsumption_resolution,[],[f1220,f358])).

fof(f358,plain,
    ( l1_pre_topc(sK1)
    | ~ spl21_0 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl21_0
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_0])])).

fof(f1220,plain,
    ( u1_pre_topc(sK1) != k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK1)
    | v2_tdlat_3(sK1)
    | ~ spl21_178 ),
    inference(superposition,[],[f270,f1151])).

fof(f1151,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl21_178 ),
    inference(avatar_component_clause,[],[f1150])).

fof(f1150,plain,
    ( spl21_178
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_178])])).

fof(f270,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f171,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',d2_tdlat_3)).

fof(f1249,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl21_136
    | ~ spl21_182
    | ~ spl21_184 ),
    inference(equality_resolution,[],[f1189])).

fof(f1189,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK1) = X1 )
    | ~ spl21_136
    | ~ spl21_182
    | ~ spl21_184 ),
    inference(subsumption_resolution,[],[f1186,f1184])).

fof(f1184,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl21_182
    | ~ spl21_184 ),
    inference(backward_demodulation,[],[f1181,f1161])).

fof(f1161,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl21_182 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f1160,plain,
    ( spl21_182
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_182])])).

fof(f1181,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl21_184 ),
    inference(equality_resolution,[],[f1167])).

fof(f1167,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK1) = X0 )
    | ~ spl21_184 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f1166,plain,
    ( spl21_184
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_184])])).

fof(f1186,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_pre_topc(sK1) = X1 )
    | ~ spl21_136
    | ~ spl21_184 ),
    inference(backward_demodulation,[],[f1181,f988])).

fof(f988,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | u1_pre_topc(sK1) = X1 )
    | ~ spl21_136 ),
    inference(superposition,[],[f283,f834])).

fof(f834,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl21_136 ),
    inference(avatar_component_clause,[],[f833])).

fof(f833,plain,
    ( spl21_136
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_136])])).

fof(f283,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',free_g1_pre_topc)).

fof(f1209,plain,
    ( spl21_188
    | ~ spl21_182
    | ~ spl21_184 ),
    inference(avatar_split_clause,[],[f1184,f1166,f1160,f1207])).

fof(f1207,plain,
    ( spl21_188
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_188])])).

fof(f1202,plain,
    ( spl21_178
    | ~ spl21_184 ),
    inference(avatar_split_clause,[],[f1181,f1166,f1150])).

fof(f1196,plain,
    ( spl21_186
    | ~ spl21_136
    | ~ spl21_184 ),
    inference(avatar_split_clause,[],[f1188,f1166,f833,f1194])).

fof(f1194,plain,
    ( spl21_186
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_186])])).

fof(f1188,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK1))
    | ~ spl21_136
    | ~ spl21_184 ),
    inference(backward_demodulation,[],[f1181,f834])).

fof(f1183,plain,
    ( spl21_179
    | ~ spl21_184 ),
    inference(avatar_contradiction_clause,[],[f1182])).

fof(f1182,plain,
    ( $false
    | ~ spl21_179
    | ~ spl21_184 ),
    inference(subsumption_resolution,[],[f1181,f1148])).

fof(f1148,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK1)
    | ~ spl21_179 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f1147,plain,
    ( spl21_179
  <=> u1_struct_0(sK0) != u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_179])])).

fof(f1171,plain,
    ( ~ spl21_0
    | spl21_183 ),
    inference(avatar_contradiction_clause,[],[f1170])).

fof(f1170,plain,
    ( $false
    | ~ spl21_0
    | ~ spl21_183 ),
    inference(subsumption_resolution,[],[f1169,f358])).

fof(f1169,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl21_183 ),
    inference(resolution,[],[f1164,f297])).

fof(f297,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f200])).

fof(f200,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',dt_u1_pre_topc)).

fof(f1164,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl21_183 ),
    inference(avatar_component_clause,[],[f1163])).

fof(f1163,plain,
    ( spl21_183
  <=> ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_183])])).

fof(f1168,plain,
    ( ~ spl21_183
    | spl21_184
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f985,f833,f1166,f1163])).

fof(f985,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
        | u1_struct_0(sK1) = X0 )
    | ~ spl21_136 ),
    inference(superposition,[],[f282,f834])).

fof(f282,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f187])).

fof(f1158,plain,
    ( spl21_178
    | ~ spl21_181
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f1143,f833,f1156,f1150])).

fof(f1156,plain,
    ( spl21_181
  <=> ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_181])])).

fof(f1143,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl21_136 ),
    inference(equality_resolution,[],[f986])).

fof(f986,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | u1_struct_0(sK1) = X0 )
    | ~ spl21_136 ),
    inference(superposition,[],[f282,f834])).

fof(f1140,plain,
    ( spl21_176
    | ~ spl21_171
    | ~ spl21_70
    | spl21_73
    | ~ spl21_76
    | ~ spl21_78 ),
    inference(avatar_split_clause,[],[f977,f630,f623,f609,f602,f1108,f1138])).

fof(f1138,plain,
    ( spl21_176
  <=> v7_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_176])])).

fof(f1108,plain,
    ( spl21_171
  <=> ~ v2_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_171])])).

fof(f602,plain,
    ( spl21_70
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_70])])).

fof(f609,plain,
    ( spl21_73
  <=> ~ v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_73])])).

fof(f623,plain,
    ( spl21_76
  <=> v1_tdlat_3(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_76])])).

fof(f630,plain,
    ( spl21_78
  <=> v2_tdlat_3(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_78])])).

fof(f977,plain,
    ( ~ v2_pre_topc(sK7)
    | v7_struct_0(sK7)
    | ~ spl21_70
    | ~ spl21_73
    | ~ spl21_76
    | ~ spl21_78 ),
    inference(subsumption_resolution,[],[f976,f631])).

fof(f631,plain,
    ( v2_tdlat_3(sK7)
    | ~ spl21_78 ),
    inference(avatar_component_clause,[],[f630])).

fof(f976,plain,
    ( ~ v2_pre_topc(sK7)
    | ~ v2_tdlat_3(sK7)
    | v7_struct_0(sK7)
    | ~ spl21_70
    | ~ spl21_73
    | ~ spl21_76 ),
    inference(subsumption_resolution,[],[f975,f603])).

fof(f603,plain,
    ( l1_pre_topc(sK7)
    | ~ spl21_70 ),
    inference(avatar_component_clause,[],[f602])).

fof(f975,plain,
    ( ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_tdlat_3(sK7)
    | v7_struct_0(sK7)
    | ~ spl21_73
    | ~ spl21_76 ),
    inference(subsumption_resolution,[],[f969,f610])).

fof(f610,plain,
    ( ~ v2_struct_0(sK7)
    | ~ spl21_73 ),
    inference(avatar_component_clause,[],[f609])).

fof(f969,plain,
    ( v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ v2_tdlat_3(sK7)
    | v7_struct_0(sK7)
    | ~ spl21_76 ),
    inference(resolution,[],[f273,f624])).

fof(f624,plain,
    ( v1_tdlat_3(sK7)
    | ~ spl21_76 ),
    inference(avatar_component_clause,[],[f623])).

fof(f273,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f175])).

fof(f175,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f174])).

fof(f174,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',cc2_tex_1)).

fof(f1132,plain,
    ( spl21_172
    | ~ spl21_175
    | ~ spl21_108
    | spl21_111
    | ~ spl21_112 ),
    inference(avatar_split_clause,[],[f878,f749,f742,f735,f1130,f1124])).

fof(f1124,plain,
    ( spl21_172
  <=> v2_tdlat_3(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_172])])).

fof(f1130,plain,
    ( spl21_175
  <=> ~ v2_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_175])])).

fof(f735,plain,
    ( spl21_108
  <=> l1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_108])])).

fof(f742,plain,
    ( spl21_111
  <=> ~ v2_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_111])])).

fof(f749,plain,
    ( spl21_112
  <=> v7_struct_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_112])])).

fof(f878,plain,
    ( ~ v2_pre_topc(sK17)
    | v2_tdlat_3(sK17)
    | ~ spl21_108
    | ~ spl21_111
    | ~ spl21_112 ),
    inference(subsumption_resolution,[],[f877,f736])).

fof(f736,plain,
    ( l1_pre_topc(sK17)
    | ~ spl21_108 ),
    inference(avatar_component_clause,[],[f735])).

fof(f877,plain,
    ( ~ v2_pre_topc(sK17)
    | v2_tdlat_3(sK17)
    | ~ l1_pre_topc(sK17)
    | ~ spl21_111
    | ~ spl21_112 ),
    inference(subsumption_resolution,[],[f873,f743])).

fof(f743,plain,
    ( ~ v2_struct_0(sK17)
    | ~ spl21_111 ),
    inference(avatar_component_clause,[],[f742])).

fof(f873,plain,
    ( v2_struct_0(sK17)
    | ~ v2_pre_topc(sK17)
    | v2_tdlat_3(sK17)
    | ~ l1_pre_topc(sK17)
    | ~ spl21_112 ),
    inference(resolution,[],[f276,f750])).

fof(f750,plain,
    ( v7_struct_0(sK17)
    | ~ spl21_112 ),
    inference(avatar_component_clause,[],[f749])).

fof(f276,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f179])).

fof(f179,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f178])).

fof(f178,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',cc4_tex_1)).

fof(f1119,plain,
    ( ~ spl21_70
    | ~ spl21_78
    | spl21_171 ),
    inference(avatar_contradiction_clause,[],[f1118])).

fof(f1118,plain,
    ( $false
    | ~ spl21_70
    | ~ spl21_78
    | ~ spl21_171 ),
    inference(subsumption_resolution,[],[f1117,f603])).

fof(f1117,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ spl21_78
    | ~ spl21_171 ),
    inference(subsumption_resolution,[],[f1116,f631])).

fof(f1116,plain,
    ( ~ v2_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ spl21_171 ),
    inference(resolution,[],[f1109,f279])).

fof(f279,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f183])).

fof(f183,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',cc2_tdlat_3)).

fof(f1109,plain,
    ( ~ v2_pre_topc(sK7)
    | ~ spl21_171 ),
    inference(avatar_component_clause,[],[f1108])).

fof(f1115,plain,
    ( ~ spl21_70
    | ~ spl21_78
    | spl21_169 ),
    inference(avatar_contradiction_clause,[],[f1114])).

fof(f1114,plain,
    ( $false
    | ~ spl21_70
    | ~ spl21_78
    | ~ spl21_169 ),
    inference(subsumption_resolution,[],[f1113,f603])).

fof(f1113,plain,
    ( ~ l1_pre_topc(sK7)
    | ~ spl21_78
    | ~ spl21_169 ),
    inference(subsumption_resolution,[],[f1112,f631])).

fof(f1112,plain,
    ( ~ v2_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ spl21_169 ),
    inference(resolution,[],[f1100,f280])).

fof(f280,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f184])).

fof(f184,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v3_tdlat_3(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',cc4_tdlat_3)).

fof(f1100,plain,
    ( ~ v3_tdlat_3(sK7)
    | ~ spl21_169 ),
    inference(avatar_component_clause,[],[f1099])).

fof(f1099,plain,
    ( spl21_169
  <=> ~ v3_tdlat_3(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_169])])).

fof(f1110,plain,
    ( spl21_168
    | ~ spl21_171
    | ~ spl21_70
    | spl21_73
    | ~ spl21_76 ),
    inference(avatar_split_clause,[],[f871,f623,f609,f602,f1108,f1102])).

fof(f1102,plain,
    ( spl21_168
  <=> v3_tdlat_3(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_168])])).

fof(f871,plain,
    ( ~ v2_pre_topc(sK7)
    | v3_tdlat_3(sK7)
    | ~ spl21_70
    | ~ spl21_73
    | ~ spl21_76 ),
    inference(subsumption_resolution,[],[f870,f603])).

fof(f870,plain,
    ( ~ v2_pre_topc(sK7)
    | v3_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ spl21_73
    | ~ spl21_76 ),
    inference(subsumption_resolution,[],[f863,f610])).

fof(f863,plain,
    ( v2_struct_0(sK7)
    | ~ v2_pre_topc(sK7)
    | v3_tdlat_3(sK7)
    | ~ l1_pre_topc(sK7)
    | ~ spl21_76 ),
    inference(resolution,[],[f274,f624])).

fof(f274,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,plain,(
    ! [X0] :
      ( ( ~ v2_tdlat_3(X0)
        & ~ v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f176])).

fof(f176,plain,(
    ! [X0] :
      ( ( ~ v2_tdlat_3(X0)
        & ~ v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( ~ v2_tdlat_3(X0)
          & ~ v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',cc5_tex_1)).

fof(f1094,plain,
    ( spl21_166
    | ~ spl21_8
    | spl21_11
    | ~ spl21_14
    | ~ spl21_16
    | ~ spl21_18 ),
    inference(avatar_split_clause,[],[f974,f420,f413,f406,f392,f385,f1092])).

fof(f1092,plain,
    ( spl21_166
  <=> v7_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_166])])).

fof(f385,plain,
    ( spl21_8
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_8])])).

fof(f392,plain,
    ( spl21_11
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_11])])).

fof(f406,plain,
    ( spl21_14
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_14])])).

fof(f413,plain,
    ( spl21_16
  <=> v1_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_16])])).

fof(f420,plain,
    ( spl21_18
  <=> v2_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_18])])).

fof(f974,plain,
    ( v7_struct_0(sK2)
    | ~ spl21_8
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_16
    | ~ spl21_18 ),
    inference(subsumption_resolution,[],[f973,f421])).

fof(f421,plain,
    ( v2_tdlat_3(sK2)
    | ~ spl21_18 ),
    inference(avatar_component_clause,[],[f420])).

fof(f973,plain,
    ( ~ v2_tdlat_3(sK2)
    | v7_struct_0(sK2)
    | ~ spl21_8
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f972,f386])).

fof(f386,plain,
    ( l1_pre_topc(sK2)
    | ~ spl21_8 ),
    inference(avatar_component_clause,[],[f385])).

fof(f972,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v7_struct_0(sK2)
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f971,f407])).

fof(f407,plain,
    ( v2_pre_topc(sK2)
    | ~ spl21_14 ),
    inference(avatar_component_clause,[],[f406])).

fof(f971,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v7_struct_0(sK2)
    | ~ spl21_11
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f967,f393])).

fof(f393,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl21_11 ),
    inference(avatar_component_clause,[],[f392])).

fof(f967,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v7_struct_0(sK2)
    | ~ spl21_16 ),
    inference(resolution,[],[f273,f414])).

fof(f414,plain,
    ( v1_tdlat_3(sK2)
    | ~ spl21_16 ),
    inference(avatar_component_clause,[],[f413])).

fof(f1087,plain,
    ( ~ spl21_165
    | ~ spl21_58
    | spl21_61
    | ~ spl21_64
    | spl21_67 ),
    inference(avatar_split_clause,[],[f892,f588,f581,f567,f560,f1085])).

fof(f1085,plain,
    ( spl21_165
  <=> ~ v7_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_165])])).

fof(f560,plain,
    ( spl21_58
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_58])])).

fof(f567,plain,
    ( spl21_61
  <=> ~ v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_61])])).

fof(f581,plain,
    ( spl21_64
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_64])])).

fof(f588,plain,
    ( spl21_67
  <=> ~ v1_tdlat_3(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_67])])).

fof(f892,plain,
    ( ~ v7_struct_0(sK6)
    | ~ spl21_58
    | ~ spl21_61
    | ~ spl21_64
    | ~ spl21_67 ),
    inference(subsumption_resolution,[],[f891,f561])).

fof(f561,plain,
    ( l1_pre_topc(sK6)
    | ~ spl21_58 ),
    inference(avatar_component_clause,[],[f560])).

fof(f891,plain,
    ( ~ v7_struct_0(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ spl21_61
    | ~ spl21_64
    | ~ spl21_67 ),
    inference(subsumption_resolution,[],[f890,f582])).

fof(f582,plain,
    ( v2_pre_topc(sK6)
    | ~ spl21_64 ),
    inference(avatar_component_clause,[],[f581])).

fof(f890,plain,
    ( ~ v7_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ spl21_61
    | ~ spl21_67 ),
    inference(subsumption_resolution,[],[f882,f568])).

fof(f568,plain,
    ( ~ v2_struct_0(sK6)
    | ~ spl21_61 ),
    inference(avatar_component_clause,[],[f567])).

fof(f882,plain,
    ( v2_struct_0(sK6)
    | ~ v7_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_pre_topc(sK6)
    | ~ spl21_67 ),
    inference(resolution,[],[f277,f589])).

fof(f589,plain,
    ( ~ v1_tdlat_3(sK6)
    | ~ spl21_67 ),
    inference(avatar_component_clause,[],[f588])).

fof(f277,plain,(
    ! [X0] :
      ( v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f180])).

fof(f180,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',cc1_tex_1)).

fof(f1080,plain,
    ( ~ spl21_163
    | ~ spl21_44
    | spl21_47
    | ~ spl21_50
    | spl21_53 ),
    inference(avatar_split_clause,[],[f889,f539,f532,f518,f511,f1078])).

fof(f1078,plain,
    ( spl21_163
  <=> ~ v7_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_163])])).

fof(f511,plain,
    ( spl21_44
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_44])])).

fof(f518,plain,
    ( spl21_47
  <=> ~ v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_47])])).

fof(f532,plain,
    ( spl21_50
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_50])])).

fof(f539,plain,
    ( spl21_53
  <=> ~ v1_tdlat_3(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_53])])).

fof(f889,plain,
    ( ~ v7_struct_0(sK5)
    | ~ spl21_44
    | ~ spl21_47
    | ~ spl21_50
    | ~ spl21_53 ),
    inference(subsumption_resolution,[],[f888,f512])).

fof(f512,plain,
    ( l1_pre_topc(sK5)
    | ~ spl21_44 ),
    inference(avatar_component_clause,[],[f511])).

fof(f888,plain,
    ( ~ v7_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl21_47
    | ~ spl21_50
    | ~ spl21_53 ),
    inference(subsumption_resolution,[],[f887,f533])).

fof(f533,plain,
    ( v2_pre_topc(sK5)
    | ~ spl21_50 ),
    inference(avatar_component_clause,[],[f532])).

fof(f887,plain,
    ( ~ v7_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl21_47
    | ~ spl21_53 ),
    inference(subsumption_resolution,[],[f881,f519])).

fof(f519,plain,
    ( ~ v2_struct_0(sK5)
    | ~ spl21_47 ),
    inference(avatar_component_clause,[],[f518])).

fof(f881,plain,
    ( v2_struct_0(sK5)
    | ~ v7_struct_0(sK5)
    | ~ v2_pre_topc(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ spl21_53 ),
    inference(resolution,[],[f277,f540])).

fof(f540,plain,
    ( ~ v1_tdlat_3(sK5)
    | ~ spl21_53 ),
    inference(avatar_component_clause,[],[f539])).

fof(f1073,plain,
    ( ~ spl21_161
    | ~ spl21_32
    | spl21_35
    | ~ spl21_38
    | spl21_41 ),
    inference(avatar_split_clause,[],[f886,f497,f490,f476,f469,f1071])).

fof(f1071,plain,
    ( spl21_161
  <=> ~ v7_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_161])])).

fof(f469,plain,
    ( spl21_32
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_32])])).

fof(f476,plain,
    ( spl21_35
  <=> ~ v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_35])])).

fof(f490,plain,
    ( spl21_38
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_38])])).

fof(f497,plain,
    ( spl21_41
  <=> ~ v1_tdlat_3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_41])])).

fof(f886,plain,
    ( ~ v7_struct_0(sK4)
    | ~ spl21_32
    | ~ spl21_35
    | ~ spl21_38
    | ~ spl21_41 ),
    inference(subsumption_resolution,[],[f885,f470])).

fof(f470,plain,
    ( l1_pre_topc(sK4)
    | ~ spl21_32 ),
    inference(avatar_component_clause,[],[f469])).

fof(f885,plain,
    ( ~ v7_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl21_35
    | ~ spl21_38
    | ~ spl21_41 ),
    inference(subsumption_resolution,[],[f884,f491])).

fof(f491,plain,
    ( v2_pre_topc(sK4)
    | ~ spl21_38 ),
    inference(avatar_component_clause,[],[f490])).

fof(f884,plain,
    ( ~ v7_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl21_35
    | ~ spl21_41 ),
    inference(subsumption_resolution,[],[f880,f477])).

fof(f477,plain,
    ( ~ v2_struct_0(sK4)
    | ~ spl21_35 ),
    inference(avatar_component_clause,[],[f476])).

fof(f880,plain,
    ( v2_struct_0(sK4)
    | ~ v7_struct_0(sK4)
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl21_41 ),
    inference(resolution,[],[f277,f498])).

fof(f498,plain,
    ( ~ v1_tdlat_3(sK4)
    | ~ spl21_41 ),
    inference(avatar_component_clause,[],[f497])).

fof(f1066,plain,
    ( spl21_158
    | ~ spl21_98
    | spl21_101
    | ~ spl21_102
    | ~ spl21_106 ),
    inference(avatar_split_clause,[],[f876,f728,f714,f707,f700,f1064])).

fof(f1064,plain,
    ( spl21_158
  <=> v2_tdlat_3(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_158])])).

fof(f700,plain,
    ( spl21_98
  <=> l1_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_98])])).

fof(f707,plain,
    ( spl21_101
  <=> ~ v2_struct_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_101])])).

fof(f714,plain,
    ( spl21_102
  <=> v7_struct_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_102])])).

fof(f728,plain,
    ( spl21_106
  <=> v2_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_106])])).

fof(f876,plain,
    ( v2_tdlat_3(sK16)
    | ~ spl21_98
    | ~ spl21_101
    | ~ spl21_102
    | ~ spl21_106 ),
    inference(subsumption_resolution,[],[f875,f701])).

fof(f701,plain,
    ( l1_pre_topc(sK16)
    | ~ spl21_98 ),
    inference(avatar_component_clause,[],[f700])).

fof(f875,plain,
    ( v2_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl21_101
    | ~ spl21_102
    | ~ spl21_106 ),
    inference(subsumption_resolution,[],[f874,f729])).

fof(f729,plain,
    ( v2_pre_topc(sK16)
    | ~ spl21_106 ),
    inference(avatar_component_clause,[],[f728])).

fof(f874,plain,
    ( ~ v2_pre_topc(sK16)
    | v2_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl21_101
    | ~ spl21_102 ),
    inference(subsumption_resolution,[],[f872,f708])).

fof(f708,plain,
    ( ~ v2_struct_0(sK16)
    | ~ spl21_101 ),
    inference(avatar_component_clause,[],[f707])).

fof(f872,plain,
    ( v2_struct_0(sK16)
    | ~ v2_pre_topc(sK16)
    | v2_tdlat_3(sK16)
    | ~ l1_pre_topc(sK16)
    | ~ spl21_102 ),
    inference(resolution,[],[f276,f715])).

fof(f715,plain,
    ( v7_struct_0(sK16)
    | ~ spl21_102 ),
    inference(avatar_component_clause,[],[f714])).

fof(f1059,plain,
    ( spl21_156
    | ~ spl21_20
    | spl21_23
    | ~ spl21_26
    | ~ spl21_28 ),
    inference(avatar_split_clause,[],[f869,f455,f448,f434,f427,f1057])).

fof(f1057,plain,
    ( spl21_156
  <=> v3_tdlat_3(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_156])])).

fof(f427,plain,
    ( spl21_20
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_20])])).

fof(f434,plain,
    ( spl21_23
  <=> ~ v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_23])])).

fof(f448,plain,
    ( spl21_26
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_26])])).

fof(f455,plain,
    ( spl21_28
  <=> v1_tdlat_3(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_28])])).

fof(f869,plain,
    ( v3_tdlat_3(sK3)
    | ~ spl21_20
    | ~ spl21_23
    | ~ spl21_26
    | ~ spl21_28 ),
    inference(subsumption_resolution,[],[f868,f428])).

fof(f428,plain,
    ( l1_pre_topc(sK3)
    | ~ spl21_20 ),
    inference(avatar_component_clause,[],[f427])).

fof(f868,plain,
    ( v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl21_23
    | ~ spl21_26
    | ~ spl21_28 ),
    inference(subsumption_resolution,[],[f867,f449])).

fof(f449,plain,
    ( v2_pre_topc(sK3)
    | ~ spl21_26 ),
    inference(avatar_component_clause,[],[f448])).

fof(f867,plain,
    ( ~ v2_pre_topc(sK3)
    | v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl21_23
    | ~ spl21_28 ),
    inference(subsumption_resolution,[],[f862,f435])).

fof(f435,plain,
    ( ~ v2_struct_0(sK3)
    | ~ spl21_23 ),
    inference(avatar_component_clause,[],[f434])).

fof(f862,plain,
    ( v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | v3_tdlat_3(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl21_28 ),
    inference(resolution,[],[f274,f456])).

fof(f456,plain,
    ( v1_tdlat_3(sK3)
    | ~ spl21_28 ),
    inference(avatar_component_clause,[],[f455])).

fof(f1052,plain,
    ( spl21_154
    | ~ spl21_8
    | spl21_11
    | ~ spl21_14
    | ~ spl21_16 ),
    inference(avatar_split_clause,[],[f866,f413,f406,f392,f385,f1050])).

fof(f1050,plain,
    ( spl21_154
  <=> v3_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_154])])).

fof(f866,plain,
    ( v3_tdlat_3(sK2)
    | ~ spl21_8
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f865,f386])).

fof(f865,plain,
    ( v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl21_11
    | ~ spl21_14
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f864,f407])).

fof(f864,plain,
    ( ~ v2_pre_topc(sK2)
    | v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl21_11
    | ~ spl21_16 ),
    inference(subsumption_resolution,[],[f861,f393])).

fof(f861,plain,
    ( v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl21_16 ),
    inference(resolution,[],[f274,f414])).

fof(f1045,plain,
    ( spl21_146
    | ~ spl21_153
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f910,f833,f357,f1043,f919])).

fof(f919,plain,
    ( spl21_146
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_146])])).

fof(f1043,plain,
    ( spl21_153
  <=> ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_153])])).

fof(f910,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_struct_0(sK1)
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(subsumption_resolution,[],[f909,f358])).

fof(f909,plain,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl21_136 ),
    inference(superposition,[],[f294,f834])).

fof(f294,plain,(
    ! [X0] :
      ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f197])).

fof(f197,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f196])).

fof(f196,plain,(
    ! [X0] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f96])).

fof(f96,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & ~ v2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',fc7_pre_topc)).

fof(f1036,plain,
    ( spl21_150
    | ~ spl21_2
    | ~ spl21_6 ),
    inference(avatar_split_clause,[],[f926,f378,f364,f1034])).

fof(f364,plain,
    ( spl21_2
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_2])])).

fof(f378,plain,
    ( spl21_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_6])])).

fof(f926,plain,
    ( u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl21_2
    | ~ spl21_6 ),
    inference(subsumption_resolution,[],[f922,f379])).

fof(f379,plain,
    ( l1_pre_topc(sK0)
    | ~ spl21_6 ),
    inference(avatar_component_clause,[],[f378])).

fof(f922,plain,
    ( u1_pre_topc(sK0) = k2_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl21_2 ),
    inference(resolution,[],[f271,f365])).

fof(f365,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl21_2 ),
    inference(avatar_component_clause,[],[f364])).

fof(f271,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | u1_pre_topc(X0) = k2_tarski(k1_xboole_0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f171])).

fof(f984,plain,
    ( spl21_148
    | ~ spl21_6
    | spl21_145 ),
    inference(avatar_split_clause,[],[f964,f902,f378,f982])).

fof(f982,plain,
    ( spl21_148
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_148])])).

fof(f902,plain,
    ( spl21_145
  <=> ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_145])])).

fof(f964,plain,
    ( v2_struct_0(sK0)
    | ~ spl21_6
    | ~ spl21_145 ),
    inference(subsumption_resolution,[],[f962,f379])).

fof(f962,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl21_145 ),
    inference(resolution,[],[f903,f295])).

fof(f295,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f197])).

fof(f903,plain,
    ( ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl21_145 ),
    inference(avatar_component_clause,[],[f902])).

fof(f921,plain,
    ( spl21_146
    | ~ spl21_0
    | ~ spl21_136
    | spl21_145 ),
    inference(avatar_split_clause,[],[f913,f902,f833,f357,f919])).

fof(f913,plain,
    ( v2_struct_0(sK1)
    | ~ spl21_0
    | ~ spl21_136
    | ~ spl21_145 ),
    inference(subsumption_resolution,[],[f912,f358])).

fof(f912,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl21_136
    | ~ spl21_145 ),
    inference(subsumption_resolution,[],[f911,f903])).

fof(f911,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl21_136 ),
    inference(superposition,[],[f295,f834])).

fof(f907,plain,
    ( ~ spl21_143
    | spl21_144
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f894,f833,f357,f905,f899])).

fof(f899,plain,
    ( spl21_143
  <=> ~ v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_143])])).

fof(f905,plain,
    ( spl21_144
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_144])])).

fof(f894,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(subsumption_resolution,[],[f893,f358])).

fof(f893,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl21_136 ),
    inference(superposition,[],[f292,f834])).

fof(f292,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f195])).

fof(f195,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f194])).

fof(f194,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f94])).

fof(f94,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',fc6_pre_topc)).

fof(f860,plain,
    ( spl21_140
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(avatar_split_clause,[],[f853,f833,f357,f858])).

fof(f858,plain,
    ( spl21_140
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_140])])).

fof(f853,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl21_0
    | ~ spl21_136 ),
    inference(subsumption_resolution,[],[f852,f358])).

fof(f852,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl21_136 ),
    inference(superposition,[],[f850,f834])).

fof(f850,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f297,f291])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',dt_g1_pre_topc)).

fof(f842,plain,(
    spl21_138 ),
    inference(avatar_split_clause,[],[f287,f840])).

fof(f840,plain,
    ( spl21_138
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_138])])).

fof(f287,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

fof(f72,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',d2_xboole_0)).

fof(f835,plain,(
    spl21_136 ),
    inference(avatar_split_clause,[],[f230,f833])).

fof(f230,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f170])).

fof(f170,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f169])).

fof(f169,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tdlat_3(X1)
          & v2_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',t18_tex_2)).

fof(f828,plain,(
    spl21_134 ),
    inference(avatar_split_clause,[],[f351,f826])).

fof(f826,plain,
    ( spl21_134
  <=> l1_pre_topc(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_134])])).

fof(f351,plain,(
    l1_pre_topc(sK20) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',existence_l1_pre_topc)).

fof(f821,plain,(
    spl21_132 ),
    inference(avatar_split_clause,[],[f350,f819])).

fof(f819,plain,
    ( spl21_132
  <=> v1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_132])])).

fof(f350,plain,(
    v1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc2_tex_1)).

fof(f814,plain,(
    ~ spl21_131 ),
    inference(avatar_split_clause,[],[f349,f812])).

fof(f812,plain,
    ( spl21_131
  <=> ~ v7_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_131])])).

fof(f349,plain,(
    ~ v7_struct_0(sK19) ),
    inference(cnf_transformation,[],[f124])).

fof(f807,plain,(
    ~ spl21_129 ),
    inference(avatar_split_clause,[],[f348,f805])).

fof(f805,plain,
    ( spl21_129
  <=> ~ v2_struct_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_129])])).

fof(f348,plain,(
    ~ v2_struct_0(sK19) ),
    inference(cnf_transformation,[],[f124])).

fof(f800,plain,(
    spl21_126 ),
    inference(avatar_split_clause,[],[f347,f798])).

fof(f798,plain,
    ( spl21_126
  <=> l1_pre_topc(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_126])])).

fof(f347,plain,(
    l1_pre_topc(sK19) ),
    inference(cnf_transformation,[],[f124])).

fof(f793,plain,(
    spl21_124 ),
    inference(avatar_split_clause,[],[f346,f791])).

fof(f791,plain,
    ( spl21_124
  <=> v2_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_124])])).

fof(f346,plain,(
    v2_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc4_tex_1)).

fof(f786,plain,(
    spl21_122 ),
    inference(avatar_split_clause,[],[f345,f784])).

fof(f784,plain,
    ( spl21_122
  <=> v1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_122])])).

fof(f345,plain,(
    v1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f140])).

fof(f779,plain,(
    ~ spl21_121 ),
    inference(avatar_split_clause,[],[f344,f777])).

fof(f777,plain,
    ( spl21_121
  <=> ~ v7_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_121])])).

fof(f344,plain,(
    ~ v7_struct_0(sK18) ),
    inference(cnf_transformation,[],[f140])).

fof(f772,plain,(
    ~ spl21_119 ),
    inference(avatar_split_clause,[],[f343,f770])).

fof(f770,plain,
    ( spl21_119
  <=> ~ v2_struct_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_119])])).

fof(f343,plain,(
    ~ v2_struct_0(sK18) ),
    inference(cnf_transformation,[],[f140])).

fof(f765,plain,(
    spl21_116 ),
    inference(avatar_split_clause,[],[f342,f763])).

fof(f763,plain,
    ( spl21_116
  <=> l1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_116])])).

fof(f342,plain,(
    l1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f140])).

fof(f758,plain,(
    spl21_114 ),
    inference(avatar_split_clause,[],[f341,f756])).

fof(f756,plain,
    ( spl21_114
  <=> v1_pre_topc(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_114])])).

fof(f341,plain,(
    v1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc1_tex_1)).

fof(f751,plain,(
    spl21_112 ),
    inference(avatar_split_clause,[],[f340,f749])).

fof(f340,plain,(
    v7_struct_0(sK17) ),
    inference(cnf_transformation,[],[f112])).

fof(f744,plain,(
    ~ spl21_111 ),
    inference(avatar_split_clause,[],[f339,f742])).

fof(f339,plain,(
    ~ v2_struct_0(sK17) ),
    inference(cnf_transformation,[],[f112])).

fof(f737,plain,(
    spl21_108 ),
    inference(avatar_split_clause,[],[f338,f735])).

fof(f338,plain,(
    l1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f112])).

fof(f730,plain,(
    spl21_106 ),
    inference(avatar_split_clause,[],[f337,f728])).

fof(f337,plain,(
    v2_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f133])).

fof(f133,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc3_tex_1)).

fof(f723,plain,(
    spl21_104 ),
    inference(avatar_split_clause,[],[f336,f721])).

fof(f721,plain,
    ( spl21_104
  <=> v1_pre_topc(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_104])])).

fof(f336,plain,(
    v1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f133])).

fof(f716,plain,(
    spl21_102 ),
    inference(avatar_split_clause,[],[f335,f714])).

fof(f335,plain,(
    v7_struct_0(sK16) ),
    inference(cnf_transformation,[],[f133])).

fof(f709,plain,(
    ~ spl21_101 ),
    inference(avatar_split_clause,[],[f334,f707])).

fof(f334,plain,(
    ~ v2_struct_0(sK16) ),
    inference(cnf_transformation,[],[f133])).

fof(f702,plain,(
    spl21_98 ),
    inference(avatar_split_clause,[],[f333,f700])).

fof(f333,plain,(
    l1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f133])).

fof(f695,plain,(
    spl21_96 ),
    inference(avatar_split_clause,[],[f332,f693])).

fof(f693,plain,
    ( spl21_96
  <=> v2_pre_topc(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_96])])).

fof(f332,plain,(
    v2_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,axiom,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc2_pre_topc)).

fof(f688,plain,(
    spl21_94 ),
    inference(avatar_split_clause,[],[f331,f686])).

fof(f686,plain,
    ( spl21_94
  <=> v1_pre_topc(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_94])])).

fof(f331,plain,(
    v1_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f119])).

fof(f681,plain,(
    ~ spl21_93 ),
    inference(avatar_split_clause,[],[f330,f679])).

fof(f679,plain,
    ( spl21_93
  <=> ~ v2_struct_0(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_93])])).

fof(f330,plain,(
    ~ v2_struct_0(sK15) ),
    inference(cnf_transformation,[],[f119])).

fof(f674,plain,(
    spl21_90 ),
    inference(avatar_split_clause,[],[f329,f672])).

fof(f672,plain,
    ( spl21_90
  <=> l1_pre_topc(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_90])])).

fof(f329,plain,(
    l1_pre_topc(sK15) ),
    inference(cnf_transformation,[],[f119])).

fof(f667,plain,(
    spl21_88 ),
    inference(avatar_split_clause,[],[f328,f665])).

fof(f665,plain,
    ( spl21_88
  <=> v1_pre_topc(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_88])])).

fof(f328,plain,(
    v1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc1_pre_topc)).

fof(f660,plain,(
    spl21_86 ),
    inference(avatar_split_clause,[],[f327,f658])).

fof(f658,plain,
    ( spl21_86
  <=> l1_pre_topc(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_86])])).

fof(f327,plain,(
    l1_pre_topc(sK14) ),
    inference(cnf_transformation,[],[f107])).

fof(f653,plain,(
    spl21_84 ),
    inference(avatar_split_clause,[],[f326,f651])).

fof(f651,plain,
    ( spl21_84
  <=> v1_pre_topc(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_84])])).

fof(f326,plain,(
    v1_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,axiom,(
    ? [X0] :
      ( v1_pre_topc(X0)
      & v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc11_pre_topc)).

fof(f646,plain,(
    spl21_82 ),
    inference(avatar_split_clause,[],[f325,f644])).

fof(f644,plain,
    ( spl21_82
  <=> v2_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_82])])).

fof(f325,plain,(
    v2_struct_0(sK13) ),
    inference(cnf_transformation,[],[f104])).

fof(f639,plain,(
    spl21_80 ),
    inference(avatar_split_clause,[],[f324,f637])).

fof(f637,plain,
    ( spl21_80
  <=> l1_pre_topc(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_80])])).

fof(f324,plain,(
    l1_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f104])).

fof(f632,plain,(
    spl21_78 ),
    inference(avatar_split_clause,[],[f269,f630])).

fof(f269,plain,(
    v2_tdlat_3(sK7) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,axiom,(
    ? [X0] :
      ( v2_tdlat_3(X0)
      & v1_tdlat_3(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc1_tdlat_3)).

fof(f625,plain,(
    spl21_76 ),
    inference(avatar_split_clause,[],[f268,f623])).

fof(f268,plain,(
    v1_tdlat_3(sK7) ),
    inference(cnf_transformation,[],[f111])).

fof(f618,plain,(
    spl21_74 ),
    inference(avatar_split_clause,[],[f267,f616])).

fof(f616,plain,
    ( spl21_74
  <=> v1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_74])])).

fof(f267,plain,(
    v1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f111])).

fof(f611,plain,(
    ~ spl21_73 ),
    inference(avatar_split_clause,[],[f266,f609])).

fof(f266,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f111])).

fof(f604,plain,(
    spl21_70 ),
    inference(avatar_split_clause,[],[f265,f602])).

fof(f265,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f111])).

fof(f597,plain,(
    ~ spl21_69 ),
    inference(avatar_split_clause,[],[f264,f595])).

fof(f595,plain,
    ( spl21_69
  <=> ~ v2_tdlat_3(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_69])])).

fof(f264,plain,(
    ~ v2_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f153])).

fof(f153,axiom,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & ~ v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc7_tex_1)).

fof(f590,plain,(
    ~ spl21_67 ),
    inference(avatar_split_clause,[],[f263,f588])).

fof(f263,plain,(
    ~ v1_tdlat_3(sK6) ),
    inference(cnf_transformation,[],[f153])).

fof(f583,plain,(
    spl21_64 ),
    inference(avatar_split_clause,[],[f262,f581])).

fof(f262,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f153])).

fof(f576,plain,(
    spl21_62 ),
    inference(avatar_split_clause,[],[f261,f574])).

fof(f574,plain,
    ( spl21_62
  <=> v1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_62])])).

fof(f261,plain,(
    v1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f153])).

fof(f569,plain,(
    ~ spl21_61 ),
    inference(avatar_split_clause,[],[f260,f567])).

fof(f260,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f153])).

fof(f562,plain,(
    spl21_58 ),
    inference(avatar_split_clause,[],[f259,f560])).

fof(f259,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f153])).

fof(f555,plain,(
    spl21_56 ),
    inference(avatar_split_clause,[],[f258,f553])).

fof(f553,plain,
    ( spl21_56
  <=> v3_tdlat_3(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_56])])).

fof(f258,plain,(
    v3_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,axiom,(
    ? [X0] :
      ( v3_tdlat_3(X0)
      & ~ v2_tdlat_3(X0)
      & ~ v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc8_tex_1)).

fof(f548,plain,(
    ~ spl21_55 ),
    inference(avatar_split_clause,[],[f257,f546])).

fof(f546,plain,
    ( spl21_55
  <=> ~ v2_tdlat_3(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_55])])).

fof(f257,plain,(
    ~ v2_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f156])).

fof(f541,plain,(
    ~ spl21_53 ),
    inference(avatar_split_clause,[],[f256,f539])).

fof(f256,plain,(
    ~ v1_tdlat_3(sK5) ),
    inference(cnf_transformation,[],[f156])).

fof(f534,plain,(
    spl21_50 ),
    inference(avatar_split_clause,[],[f255,f532])).

fof(f255,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f156])).

fof(f527,plain,(
    spl21_48 ),
    inference(avatar_split_clause,[],[f254,f525])).

fof(f525,plain,
    ( spl21_48
  <=> v1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_48])])).

fof(f254,plain,(
    v1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f156])).

fof(f520,plain,(
    ~ spl21_47 ),
    inference(avatar_split_clause,[],[f253,f518])).

fof(f253,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f156])).

fof(f513,plain,(
    spl21_44 ),
    inference(avatar_split_clause,[],[f252,f511])).

fof(f252,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f156])).

fof(f506,plain,(
    spl21_42 ),
    inference(avatar_split_clause,[],[f251,f504])).

fof(f504,plain,
    ( spl21_42
  <=> v2_tdlat_3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_42])])).

fof(f251,plain,(
    v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f148])).

fof(f148,axiom,(
    ? [X0] :
      ( v2_tdlat_3(X0)
      & ~ v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc6_tex_1)).

fof(f499,plain,(
    ~ spl21_41 ),
    inference(avatar_split_clause,[],[f250,f497])).

fof(f250,plain,(
    ~ v1_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f148])).

fof(f492,plain,(
    spl21_38 ),
    inference(avatar_split_clause,[],[f249,f490])).

fof(f249,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f148])).

fof(f485,plain,(
    spl21_36 ),
    inference(avatar_split_clause,[],[f248,f483])).

fof(f483,plain,
    ( spl21_36
  <=> v1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_36])])).

fof(f248,plain,(
    v1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f148])).

fof(f478,plain,(
    ~ spl21_35 ),
    inference(avatar_split_clause,[],[f247,f476])).

fof(f247,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f148])).

fof(f471,plain,(
    spl21_32 ),
    inference(avatar_split_clause,[],[f246,f469])).

fof(f246,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f148])).

fof(f464,plain,(
    ~ spl21_31 ),
    inference(avatar_split_clause,[],[f245,f462])).

fof(f462,plain,
    ( spl21_31
  <=> ~ v2_tdlat_3(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_31])])).

fof(f245,plain,(
    ~ v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f143])).

fof(f143,axiom,(
    ? [X0] :
      ( ~ v2_tdlat_3(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc5_tex_1)).

fof(f457,plain,(
    spl21_28 ),
    inference(avatar_split_clause,[],[f244,f455])).

fof(f244,plain,(
    v1_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f143])).

fof(f450,plain,(
    spl21_26 ),
    inference(avatar_split_clause,[],[f243,f448])).

fof(f243,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f143])).

fof(f443,plain,(
    spl21_24 ),
    inference(avatar_split_clause,[],[f242,f441])).

fof(f441,plain,
    ( spl21_24
  <=> v1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_24])])).

fof(f242,plain,(
    v1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f143])).

fof(f436,plain,(
    ~ spl21_23 ),
    inference(avatar_split_clause,[],[f241,f434])).

fof(f241,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f143])).

fof(f429,plain,(
    spl21_20 ),
    inference(avatar_split_clause,[],[f240,f427])).

fof(f240,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f143])).

fof(f422,plain,(
    spl21_18 ),
    inference(avatar_split_clause,[],[f239,f420])).

fof(f239,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f132])).

fof(f132,axiom,(
    ? [X0] :
      ( v2_tdlat_3(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & v1_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t18_tex_2.p',rc3_tdlat_3)).

fof(f415,plain,(
    spl21_16 ),
    inference(avatar_split_clause,[],[f238,f413])).

fof(f238,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f132])).

fof(f408,plain,(
    spl21_14 ),
    inference(avatar_split_clause,[],[f237,f406])).

fof(f237,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f132])).

fof(f401,plain,(
    spl21_12 ),
    inference(avatar_split_clause,[],[f236,f399])).

fof(f399,plain,
    ( spl21_12
  <=> v1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl21_12])])).

fof(f236,plain,(
    v1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f132])).

fof(f394,plain,(
    ~ spl21_11 ),
    inference(avatar_split_clause,[],[f235,f392])).

fof(f235,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f132])).

fof(f387,plain,(
    spl21_8 ),
    inference(avatar_split_clause,[],[f234,f385])).

fof(f234,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f132])).

fof(f380,plain,(
    spl21_6 ),
    inference(avatar_split_clause,[],[f233,f378])).

fof(f233,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f170])).

fof(f373,plain,(
    ~ spl21_5 ),
    inference(avatar_split_clause,[],[f232,f371])).

fof(f232,plain,(
    ~ v2_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f170])).

fof(f366,plain,(
    spl21_2 ),
    inference(avatar_split_clause,[],[f231,f364])).

fof(f231,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f170])).

fof(f359,plain,(
    spl21_0 ),
    inference(avatar_split_clause,[],[f229,f357])).

fof(f229,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f170])).
%------------------------------------------------------------------------------
