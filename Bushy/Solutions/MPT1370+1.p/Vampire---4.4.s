%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t25_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:50 EDT 2019

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  400 (1099 expanded)
%              Number of leaves         :  121 ( 453 expanded)
%              Depth                    :   19
%              Number of atoms          : 1262 (4810 expanded)
%              Number of equality atoms :   74 ( 305 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f130,f137,f144,f151,f158,f165,f172,f179,f186,f193,f200,f207,f214,f221,f228,f235,f242,f249,f257,f264,f271,f280,f292,f299,f306,f313,f334,f341,f348,f356,f363,f394,f404,f414,f416,f429,f444,f463,f476,f490,f497,f505,f517,f532,f542,f552,f575,f589,f611,f625,f672,f691,f710,f720,f723,f733,f746,f755,f769,f783,f802,f811,f821,f830,f849,f858,f881,f1111,f1125,f1139])).

fof(f1139,plain,
    ( ~ spl8_2
    | spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_158
    | spl8_167 ),
    inference(avatar_contradiction_clause,[],[f1138])).

fof(f1138,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_158
    | ~ spl8_167 ),
    inference(subsumption_resolution,[],[f1137,f810])).

fof(f810,plain,
    ( v2_compts_1(sK3,sK0)
    | ~ spl8_158 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl8_158
  <=> v2_compts_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_158])])).

fof(f1137,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_32
    | ~ spl8_34
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_167 ),
    inference(subsumption_resolution,[],[f1136,f241])).

fof(f241,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl8_34
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f1136,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK3,sK0)
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_167 ),
    inference(resolution,[],[f1135,f848])).

fof(f848,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl8_167 ),
    inference(avatar_component_clause,[],[f847])).

fof(f847,plain,
    ( spl8_167
  <=> ~ v4_pre_topc(k9_relat_1(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_167])])).

fof(f1135,plain,
    ( ! [X0] :
        ( v4_pre_topc(k9_relat_1(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(X0,sK0) )
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1134,f842])).

fof(f842,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_38 ),
    inference(superposition,[],[f627,f834])).

fof(f834,plain,
    ( ! [X14] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X14) = k9_relat_1(sK2,X14)
    | ~ spl8_38 ),
    inference(resolution,[],[f110,f256])).

fof(f256,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl8_38
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',redefinition_k7_relset_1)).

fof(f627,plain,
    ( ! [X4] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_38 ),
    inference(resolution,[],[f109,f256])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',dt_k7_relset_1)).

fof(f1134,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k9_relat_1(sK2,X0),sK1)
        | ~ m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(resolution,[],[f1133,f840])).

fof(f840,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK1)
        | v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f839,f143])).

fof(f143,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl8_6
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f839,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK1)
        | v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK1) )
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f838,f150])).

fof(f150,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f838,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK1)
        | v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1) )
    | ~ spl8_14 ),
    inference(resolution,[],[f98,f171])).

fof(f171,plain,
    ( v8_pre_topc(sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl8_14
  <=> v8_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',t16_compts_1)).

fof(f1133,plain,
    ( ! [X0] :
        ( v2_compts_1(k9_relat_1(sK2,X0),sK1)
        | ~ v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f1132,f834])).

fof(f1132,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1131,f129])).

fof(f129,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl8_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1131,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1130,f136])).

fof(f136,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_5
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1130,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1129,f150])).

fof(f1129,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_10
    | ~ spl8_32
    | ~ spl8_36
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1128,f248])).

fof(f248,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl8_36
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f1128,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_10
    | ~ spl8_32
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1127,f234])).

fof(f234,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl8_32
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f1127,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v2_compts_1(X0,sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_10
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1126,f263])).

fof(f263,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl8_40
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f1126,plain,
    ( ! [X0] :
        ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v2_compts_1(X0,sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_10
    | ~ spl8_38 ),
    inference(resolution,[],[f932,f256])).

fof(f932,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2) != k2_struct_0(X2)
        | ~ v5_pre_topc(sK2,X1,X2)
        | ~ v2_compts_1(X0,X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2))
        | v2_compts_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2,X0),X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl8_10 ),
    inference(resolution,[],[f97,f157])).

fof(f157,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_10
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v2_compts_1(X1,X0)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
      | ~ v5_pre_topc(X3,X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
      | v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ( ( v2_compts_1(X1,X0)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v5_pre_topc(X3,X0,X2) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',t24_compts_1)).

fof(f1125,plain,
    ( ~ spl8_177
    | spl8_80
    | spl8_178
    | ~ spl8_172 ),
    inference(avatar_split_clause,[],[f1112,f1103,f1123,f442,f1117])).

fof(f1117,plain,
    ( spl8_177
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_177])])).

fof(f442,plain,
    ( spl8_80
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f1123,plain,
    ( spl8_178
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_178])])).

fof(f1103,plain,
    ( spl8_172
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK3))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_172])])).

fof(f1112,plain,
    ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK3))))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK3))))))
    | ~ spl8_172 ),
    inference(resolution,[],[f1104,f349])).

fof(f349,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f318,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',t2_subset)).

fof(f318,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f102,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',antisymmetry_r2_hidden)).

fof(f1104,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK3))))),u1_struct_0(sK0))
    | ~ spl8_172 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f1111,plain,
    ( spl8_172
    | spl8_174
    | spl8_110
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f1087,f474,f573,f1109,f1103])).

fof(f1109,plain,
    ( spl8_174
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_174])])).

fof(f573,plain,
    ( spl8_110
  <=> v1_xboole_0(sK4(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).

fof(f474,plain,
    ( spl8_88
  <=> ! [X7] :
        ( m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f1087,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK3)))
    | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK3)))))
    | m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(sK3))))),u1_struct_0(sK0))
    | ~ spl8_88 ),
    inference(resolution,[],[f561,f475])).

fof(f475,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,sK3)
        | m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f474])).

fof(f561,plain,(
    ! [X6] :
      ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X6))))),X6)
      | v1_xboole_0(sK4(k1_zfmisc_1(X6)))
      | v1_xboole_0(sK4(k1_zfmisc_1(sK4(k1_zfmisc_1(X6))))) ) ),
    inference(resolution,[],[f554,f472])).

fof(f472,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,sK4(k1_zfmisc_1(X9)))
      | v1_xboole_0(sK4(k1_zfmisc_1(X9)))
      | m1_subset_1(X8,X9) ) ),
    inference(resolution,[],[f367,f99])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',existence_m1_subset_1)).

fof(f367,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f107,f102])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',t4_subset)).

fof(f554,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK4(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK4(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f472,f99])).

fof(f881,plain,
    ( spl8_86
    | spl8_170
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f854,f255,f879,f461])).

fof(f461,plain,
    ( spl8_86
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f879,plain,
    ( spl8_170
  <=> ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | ~ m1_subset_1(u1_struct_0(sK1),sK4(k9_relat_1(sK2,X0)))
        | v1_xboole_0(sK4(k9_relat_1(sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_170])])).

fof(f854,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK4(k9_relat_1(sK2,X0)))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK1),sK4(k9_relat_1(sK2,X0))) )
    | ~ spl8_38 ),
    inference(resolution,[],[f852,f349])).

fof(f852,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(k9_relat_1(sK2,X0)),u1_struct_0(sK1))
        | v1_xboole_0(k9_relat_1(sK2,X0)) )
    | ~ spl8_38 ),
    inference(resolution,[],[f850,f99])).

fof(f850,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k9_relat_1(sK2,X1))
        | v1_xboole_0(k9_relat_1(sK2,X1))
        | m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_38 ),
    inference(resolution,[],[f842,f367])).

fof(f858,plain,
    ( spl8_84
    | spl8_168
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f851,f255,f856,f455])).

fof(f455,plain,
    ( spl8_84
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f856,plain,
    ( spl8_168
  <=> ! [X2] :
        ( v1_xboole_0(k9_relat_1(sK2,X2))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_relat_1(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_168])])).

fof(f851,plain,
    ( ! [X2] :
        ( v1_xboole_0(k9_relat_1(sK2,X2))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_relat_1(sK2,X2)) )
    | ~ spl8_38 ),
    inference(resolution,[],[f842,f349])).

fof(f849,plain,
    ( ~ spl8_167
    | ~ spl8_38
    | spl8_43 ),
    inference(avatar_split_clause,[],[f841,f269,f255,f847])).

fof(f269,plain,
    ( spl8_43
  <=> ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f841,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl8_38
    | ~ spl8_43 ),
    inference(superposition,[],[f270,f834])).

fof(f270,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f269])).

fof(f830,plain,
    ( spl8_160
    | ~ spl8_165
    | ~ spl8_104
    | ~ spl8_162 ),
    inference(avatar_split_clause,[],[f823,f819,f540,f828,f816])).

fof(f816,plain,
    ( spl8_160
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_160])])).

fof(f828,plain,
    ( spl8_165
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).

fof(f540,plain,
    ( spl8_104
  <=> ! [X6] :
        ( m1_subset_1(X6,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ m1_subset_1(X6,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f819,plain,
    ( spl8_162
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_162])])).

fof(f823,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2)
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl8_104
    | ~ spl8_162 ),
    inference(duplicate_literal_removal,[],[f822])).

fof(f822,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2)
    | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),sK2)
    | ~ spl8_104
    | ~ spl8_162 ),
    inference(resolution,[],[f820,f541])).

fof(f541,plain,
    ( ! [X6] :
        ( m1_subset_1(X6,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ m1_subset_1(X6,sK2) )
    | ~ spl8_104 ),
    inference(avatar_component_clause,[],[f540])).

fof(f820,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),X0)
        | ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0) )
    | ~ spl8_162 ),
    inference(avatar_component_clause,[],[f819])).

fof(f821,plain,
    ( spl8_160
    | spl8_162
    | ~ spl8_104 ),
    inference(avatar_split_clause,[],[f553,f540,f819,f816])).

fof(f553,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | v1_xboole_0(X0)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),X0) )
    | ~ spl8_104 ),
    inference(resolution,[],[f541,f349])).

fof(f811,plain,
    ( spl8_158
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_28
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f804,f240,f219,f163,f128,f809])).

fof(f163,plain,
    ( spl8_12
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f219,plain,
    ( spl8_28
  <=> v4_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f804,plain,
    ( v2_compts_1(sK3,sK0)
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_28
    | ~ spl8_34 ),
    inference(subsumption_resolution,[],[f803,f241])).

fof(f803,plain,
    ( v2_compts_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_12
    | ~ spl8_28 ),
    inference(resolution,[],[f735,f220])).

fof(f220,plain,
    ( v4_pre_topc(sK3,sK0)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f219])).

fof(f735,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f734,f129])).

fof(f734,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v2_compts_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_12 ),
    inference(resolution,[],[f96,f164])).

fof(f164,plain,
    ( v1_compts_1(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(X0)
      | ~ v4_pre_topc(X1,X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',t17_compts_1)).

fof(f802,plain,
    ( ~ spl8_157
    | ~ spl8_146
    | spl8_149 ),
    inference(avatar_split_clause,[],[f795,f741,f731,f800])).

fof(f800,plain,
    ( spl8_157
  <=> k1_xboole_0 != sK4(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_157])])).

fof(f731,plain,
    ( spl8_146
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).

fof(f741,plain,
    ( spl8_149
  <=> k1_xboole_0 != sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f795,plain,
    ( k1_xboole_0 != sK4(k1_xboole_0)
    | ~ spl8_146
    | ~ spl8_149 ),
    inference(superposition,[],[f742,f732])).

fof(f732,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_146 ),
    inference(avatar_component_clause,[],[f731])).

fof(f742,plain,
    ( k1_xboole_0 != sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl8_149 ),
    inference(avatar_component_clause,[],[f741])).

fof(f783,plain,
    ( spl8_154
    | ~ spl8_148 ),
    inference(avatar_split_clause,[],[f774,f744,f781])).

fof(f781,plain,
    ( spl8_154
  <=> m1_subset_1(k1_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).

fof(f744,plain,
    ( spl8_148
  <=> k1_xboole_0 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_148])])).

fof(f774,plain,
    ( m1_subset_1(k1_xboole_0,sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl8_148 ),
    inference(superposition,[],[f99,f745])).

fof(f745,plain,
    ( k1_xboole_0 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl8_148 ),
    inference(avatar_component_clause,[],[f744])).

fof(f769,plain,
    ( spl8_152
    | ~ spl8_146 ),
    inference(avatar_split_clause,[],[f759,f731,f767])).

fof(f767,plain,
    ( spl8_152
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_152])])).

fof(f759,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_146 ),
    inference(superposition,[],[f99,f732])).

fof(f755,plain,
    ( ~ spl8_151
    | spl8_145
    | ~ spl8_146 ),
    inference(avatar_split_clause,[],[f747,f731,f715,f753])).

fof(f753,plain,
    ( spl8_151
  <=> ~ v1_xboole_0(sK4(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).

fof(f715,plain,
    ( spl8_145
  <=> ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_145])])).

fof(f747,plain,
    ( ~ v1_xboole_0(sK4(k1_xboole_0))
    | ~ spl8_145
    | ~ spl8_146 ),
    inference(forward_demodulation,[],[f716,f732])).

fof(f716,plain,
    ( ~ v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl8_145 ),
    inference(avatar_component_clause,[],[f715])).

fof(f746,plain,
    ( spl8_148
    | ~ spl8_144 ),
    inference(avatar_split_clause,[],[f738,f718,f744])).

fof(f718,plain,
    ( spl8_144
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).

fof(f738,plain,
    ( k1_xboole_0 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl8_144 ),
    inference(resolution,[],[f719,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',t6_boole)).

fof(f719,plain,
    ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl8_144 ),
    inference(avatar_component_clause,[],[f718])).

fof(f733,plain,
    ( spl8_146
    | ~ spl8_118 ),
    inference(avatar_split_clause,[],[f726,f609,f731])).

fof(f609,plain,
    ( spl8_118
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f726,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_118 ),
    inference(resolution,[],[f610,f94])).

fof(f610,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl8_118 ),
    inference(avatar_component_clause,[],[f609])).

fof(f723,plain,(
    ~ spl8_142 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | ~ spl8_142 ),
    inference(resolution,[],[f713,f99])).

fof(f713,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl8_142 ),
    inference(avatar_component_clause,[],[f712])).

fof(f712,plain,
    ( spl8_142
  <=> ! [X0] : ~ m1_subset_1(X0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f720,plain,
    ( spl8_142
    | spl8_144
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f612,f603,f718,f712])).

fof(f603,plain,
    ( spl8_116
  <=> ! [X1] : ~ r2_hidden(X1,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f612,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
        | ~ m1_subset_1(X0,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl8_116 ),
    inference(resolution,[],[f604,f102])).

fof(f604,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl8_116 ),
    inference(avatar_component_clause,[],[f603])).

fof(f710,plain,
    ( ~ spl8_137
    | spl8_138
    | spl8_140
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f372,f361,f708,f702,f696])).

fof(f696,plain,
    ( spl8_137
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK7)),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f702,plain,
    ( spl8_138
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f708,plain,
    ( spl8_140
  <=> v1_xboole_0(u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).

fof(f361,plain,
    ( spl8_62
  <=> m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f372,plain,
    ( v1_xboole_0(u1_struct_0(sK7))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK7)),u1_struct_0(sK7))
    | ~ spl8_62 ),
    inference(resolution,[],[f349,f362])).

fof(f362,plain,
    ( m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f361])).

fof(f691,plain,
    ( ~ spl8_131
    | spl8_132
    | spl8_134
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f371,f354,f689,f683,f677])).

fof(f677,plain,
    ( spl8_131
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).

fof(f683,plain,
    ( spl8_132
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_132])])).

fof(f689,plain,
    ( spl8_134
  <=> v1_xboole_0(u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f354,plain,
    ( spl8_60
  <=> m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f371,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK6)),u1_struct_0(sK6))
    | ~ spl8_60 ),
    inference(resolution,[],[f349,f355])).

fof(f355,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f354])).

fof(f672,plain,
    ( ~ spl8_125
    | spl8_126
    | spl8_128
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f370,f346,f670,f664,f658])).

fof(f658,plain,
    ( spl8_125
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_125])])).

fof(f664,plain,
    ( spl8_126
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).

fof(f670,plain,
    ( spl8_128
  <=> v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).

fof(f346,plain,
    ( spl8_58
  <=> m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f370,plain,
    ( v1_xboole_0(u1_struct_0(sK5))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ spl8_58 ),
    inference(resolution,[],[f349,f347])).

fof(f347,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f346])).

fof(f625,plain,
    ( ~ spl8_121
    | spl8_122
    | spl8_102
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f373,f255,f537,f623,f617])).

fof(f617,plain,
    ( spl8_121
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_121])])).

fof(f623,plain,
    ( spl8_122
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f537,plain,
    ( spl8_102
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f373,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))),sK2)
    | ~ spl8_38 ),
    inference(resolution,[],[f349,f256])).

fof(f611,plain,
    ( spl8_116
    | spl8_118
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f557,f212,f609,f603])).

fof(f212,plain,
    ( spl8_26
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f557,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
        | ~ r2_hidden(X1,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl8_26 ),
    inference(resolution,[],[f554,f364])).

fof(f364,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f108,f213])).

fof(f213,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',t5_subset)).

fof(f589,plain,
    ( ~ spl8_113
    | spl8_80
    | spl8_114
    | ~ spl8_108 ),
    inference(avatar_split_clause,[],[f576,f567,f587,f442,f581])).

fof(f581,plain,
    ( spl8_113
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK4(sK4(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f587,plain,
    ( spl8_114
  <=> v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f567,plain,
    ( spl8_108
  <=> m1_subset_1(sK4(sK4(k1_zfmisc_1(sK3))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).

fof(f576,plain,
    ( v1_xboole_0(sK4(sK4(k1_zfmisc_1(sK3))))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK4(sK4(k1_zfmisc_1(sK3))))
    | ~ spl8_108 ),
    inference(resolution,[],[f568,f349])).

fof(f568,plain,
    ( m1_subset_1(sK4(sK4(k1_zfmisc_1(sK3))),u1_struct_0(sK0))
    | ~ spl8_108 ),
    inference(avatar_component_clause,[],[f567])).

fof(f575,plain,
    ( spl8_108
    | spl8_110
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f560,f474,f573,f567])).

fof(f560,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(sK3)))
    | m1_subset_1(sK4(sK4(k1_zfmisc_1(sK3))),u1_struct_0(sK0))
    | ~ spl8_88 ),
    inference(resolution,[],[f554,f475])).

fof(f552,plain,
    ( spl8_106
    | ~ spl8_102 ),
    inference(avatar_split_clause,[],[f545,f537,f550])).

fof(f550,plain,
    ( spl8_106
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).

fof(f545,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_102 ),
    inference(resolution,[],[f538,f94])).

fof(f538,plain,
    ( v1_xboole_0(sK2)
    | ~ spl8_102 ),
    inference(avatar_component_clause,[],[f537])).

fof(f542,plain,
    ( spl8_102
    | spl8_104
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f470,f255,f540,f537])).

fof(f470,plain,
    ( ! [X6] :
        ( m1_subset_1(X6,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X6,sK2) )
    | ~ spl8_38 ),
    inference(resolution,[],[f367,f256])).

fof(f532,plain,
    ( ~ spl8_99
    | spl8_80
    | spl8_100
    | ~ spl8_94 ),
    inference(avatar_split_clause,[],[f518,f503,f530,f442,f524])).

fof(f524,plain,
    ( spl8_99
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f530,plain,
    ( spl8_100
  <=> v1_xboole_0(sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).

fof(f503,plain,
    ( spl8_94
  <=> m1_subset_1(sK4(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_94])])).

fof(f518,plain,
    ( v1_xboole_0(sK4(sK3))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK4(sK3))
    | ~ spl8_94 ),
    inference(resolution,[],[f504,f349])).

fof(f504,plain,
    ( m1_subset_1(sK4(sK3),u1_struct_0(sK0))
    | ~ spl8_94 ),
    inference(avatar_component_clause,[],[f503])).

fof(f517,plain,
    ( spl8_96
    | ~ spl8_28
    | ~ spl8_90 ),
    inference(avatar_split_clause,[],[f510,f488,f219,f515])).

fof(f515,plain,
    ( spl8_96
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_96])])).

fof(f488,plain,
    ( spl8_90
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f510,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_28
    | ~ spl8_90 ),
    inference(superposition,[],[f220,f489])).

fof(f489,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_90 ),
    inference(avatar_component_clause,[],[f488])).

fof(f505,plain,
    ( spl8_94
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f498,f474,f503])).

fof(f498,plain,
    ( m1_subset_1(sK4(sK3),u1_struct_0(sK0))
    | ~ spl8_88 ),
    inference(resolution,[],[f475,f99])).

fof(f497,plain,
    ( spl8_92
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f483,f297,f262,f255,f495])).

fof(f495,plain,
    ( spl8_92
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f297,plain,
    ( spl8_48
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f483,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl8_38
    | ~ spl8_40
    | ~ spl8_48 ),
    inference(forward_demodulation,[],[f482,f298])).

fof(f298,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f297])).

fof(f482,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl8_38
    | ~ spl8_40 ),
    inference(forward_demodulation,[],[f480,f263])).

fof(f480,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl8_38 ),
    inference(resolution,[],[f105,f256])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',redefinition_k2_relset_1)).

fof(f490,plain,
    ( spl8_90
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f479,f392,f488])).

fof(f392,plain,
    ( spl8_68
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f479,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_68 ),
    inference(resolution,[],[f393,f94])).

fof(f393,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f392])).

fof(f476,plain,
    ( spl8_68
    | spl8_88
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f471,f240,f474,f392])).

fof(f471,plain,
    ( ! [X7] :
        ( m1_subset_1(X7,u1_struct_0(sK0))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(X7,sK3) )
    | ~ spl8_34 ),
    inference(resolution,[],[f367,f241])).

fof(f463,plain,
    ( ~ spl8_83
    | spl8_84
    | spl8_86
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f369,f339,f461,f455,f449])).

fof(f449,plain,
    ( spl8_83
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f339,plain,
    ( spl8_56
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f369,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl8_56 ),
    inference(resolution,[],[f349,f340])).

fof(f340,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f339])).

fof(f444,plain,
    ( ~ spl8_79
    | spl8_66
    | spl8_80
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f368,f332,f442,f386,f436])).

fof(f436,plain,
    ( spl8_79
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f386,plain,
    ( spl8_66
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f332,plain,
    ( spl8_54
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f368,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl8_54 ),
    inference(resolution,[],[f349,f333])).

fof(f333,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f332])).

fof(f429,plain,
    ( spl8_76
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f420,f412,f427])).

fof(f427,plain,
    ( spl8_76
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f412,plain,
    ( spl8_74
  <=> k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f420,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_74 ),
    inference(superposition,[],[f99,f413])).

fof(f413,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f412])).

fof(f416,plain,(
    ~ spl8_70 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl8_70 ),
    inference(resolution,[],[f397,f99])).

fof(f397,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl8_70
  <=> ! [X0] : ~ m1_subset_1(X0,sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f414,plain,
    ( spl8_74
    | ~ spl8_72 ),
    inference(avatar_split_clause,[],[f407,f402,f412])).

fof(f402,plain,
    ( spl8_72
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f407,plain,
    ( k1_xboole_0 = sK4(k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_72 ),
    inference(resolution,[],[f403,f94])).

fof(f403,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f402])).

fof(f404,plain,
    ( spl8_70
    | spl8_72
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f366,f212,f402,f396])).

fof(f366,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(k1_zfmisc_1(k1_xboole_0)))
        | ~ m1_subset_1(X0,sK4(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl8_26 ),
    inference(resolution,[],[f365,f102])).

fof(f365,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_26 ),
    inference(resolution,[],[f364,f99])).

fof(f394,plain,
    ( ~ spl8_65
    | spl8_66
    | spl8_68
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f374,f240,f392,f386,f380])).

fof(f380,plain,
    ( spl8_65
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f374,plain,
    ( v1_xboole_0(sK3)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK3)
    | ~ spl8_34 ),
    inference(resolution,[],[f349,f241])).

fof(f363,plain,
    ( spl8_62
    | ~ spl8_20
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f327,f311,f191,f361])).

fof(f191,plain,
    ( spl8_20
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f311,plain,
    ( spl8_52
  <=> u1_struct_0(sK7) = k2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f327,plain,
    ( m1_subset_1(u1_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ spl8_20
    | ~ spl8_52 ),
    inference(forward_demodulation,[],[f323,f312])).

fof(f312,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f311])).

fof(f323,plain,
    ( m1_subset_1(k2_struct_0(sK7),k1_zfmisc_1(u1_struct_0(sK7)))
    | ~ spl8_20 ),
    inference(resolution,[],[f315,f192])).

fof(f192,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f191])).

fof(f315,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f93,f95])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',dt_l1_pre_topc)).

fof(f93,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',dt_k2_struct_0)).

fof(f356,plain,
    ( spl8_60
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f326,f304,f184,f354])).

fof(f184,plain,
    ( spl8_18
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f304,plain,
    ( spl8_50
  <=> u1_struct_0(sK6) = k2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f326,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(forward_demodulation,[],[f322,f305])).

fof(f305,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6)
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f304])).

fof(f322,plain,
    ( m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl8_18 ),
    inference(resolution,[],[f315,f185])).

fof(f185,plain,
    ( l1_pre_topc(sK6)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f348,plain,
    ( spl8_58
    | ~ spl8_16
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f316,f278,f177,f346])).

fof(f177,plain,
    ( spl8_16
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f278,plain,
    ( spl8_44
  <=> u1_struct_0(sK5) = k2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f316,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl8_16
    | ~ spl8_44 ),
    inference(forward_demodulation,[],[f314,f279])).

fof(f279,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f278])).

fof(f314,plain,
    ( m1_subset_1(k2_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl8_16 ),
    inference(resolution,[],[f93,f178])).

fof(f178,plain,
    ( l1_struct_0(sK5)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f341,plain,
    ( spl8_56
    | ~ spl8_8
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f325,f297,f149,f339])).

fof(f325,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_8
    | ~ spl8_48 ),
    inference(forward_demodulation,[],[f321,f298])).

fof(f321,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_8 ),
    inference(resolution,[],[f315,f150])).

fof(f334,plain,
    ( spl8_54
    | ~ spl8_2
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f324,f290,f128,f332])).

fof(f290,plain,
    ( spl8_46
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f324,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2
    | ~ spl8_46 ),
    inference(forward_demodulation,[],[f320,f291])).

fof(f291,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f290])).

fof(f320,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_2 ),
    inference(resolution,[],[f315,f129])).

fof(f313,plain,
    ( spl8_52
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f285,f191,f311])).

fof(f285,plain,
    ( u1_struct_0(sK7) = k2_struct_0(sK7)
    | ~ spl8_20 ),
    inference(resolution,[],[f273,f192])).

fof(f273,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f92,f95])).

fof(f92,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',d3_struct_0)).

fof(f306,plain,
    ( spl8_50
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f284,f184,f304])).

fof(f284,plain,
    ( u1_struct_0(sK6) = k2_struct_0(sK6)
    | ~ spl8_18 ),
    inference(resolution,[],[f273,f185])).

fof(f299,plain,
    ( spl8_48
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f283,f149,f297])).

fof(f283,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl8_8 ),
    inference(resolution,[],[f273,f150])).

fof(f292,plain,
    ( spl8_46
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f282,f128,f290])).

fof(f282,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f273,f129])).

fof(f280,plain,
    ( spl8_44
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f272,f177,f278])).

fof(f272,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl8_16 ),
    inference(resolution,[],[f92,f178])).

fof(f271,plain,(
    ~ spl8_43 ),
    inference(avatar_split_clause,[],[f89,f269])).

fof(f89,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    & v4_pre_topc(sK3,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & v5_pre_topc(sK2,sK0,sK1)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & v8_pre_topc(sK1)
    & v1_compts_1(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f65,f64,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v5_pre_topc(X2,X0,X1)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & v8_pre_topc(X1)
                & v1_compts_1(X0)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,sK0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & v5_pre_topc(X2,sK0,X1)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3),sK1)
                & v4_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & v5_pre_topc(X2,X0,sK1)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & v8_pre_topc(sK1)
            & v1_compts_1(X0)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
              & v4_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & v5_pre_topc(X2,X0,X1)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & v8_pre_topc(X1)
          & v1_compts_1(X0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ? [X3] :
            ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3),X1)
            & v4_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & v5_pre_topc(sK2,X0,X1)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & v8_pre_topc(X1)
        & v1_compts_1(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3),X1)
        & v4_pre_topc(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v5_pre_topc(X2,X0,X1)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                       => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',t25_compts_1)).

fof(f264,plain,(
    spl8_40 ),
    inference(avatar_split_clause,[],[f85,f262])).

fof(f85,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f257,plain,(
    spl8_38 ),
    inference(avatar_split_clause,[],[f82,f255])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f249,plain,(
    spl8_36 ),
    inference(avatar_split_clause,[],[f81,f247])).

fof(f81,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f242,plain,(
    spl8_34 ),
    inference(avatar_split_clause,[],[f87,f240])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f235,plain,(
    spl8_32 ),
    inference(avatar_split_clause,[],[f86,f233])).

fof(f86,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f228,plain,(
    spl8_30 ),
    inference(avatar_split_clause,[],[f91,f226])).

fof(f226,plain,
    ( spl8_30
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f91,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',d2_xboole_0)).

fof(f221,plain,(
    spl8_28 ),
    inference(avatar_split_clause,[],[f88,f219])).

fof(f88,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f214,plain,(
    spl8_26 ),
    inference(avatar_split_clause,[],[f116,f212])).

fof(f116,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f90,f91])).

fof(f90,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',dt_o_0_0_xboole_0)).

fof(f207,plain,(
    spl8_24 ),
    inference(avatar_split_clause,[],[f115,f205])).

fof(f205,plain,
    ( spl8_24
  <=> v2_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f115,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,
    ( v2_pre_topc(sK7)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f73])).

fof(f73,plain,
    ( ? [X0] :
        ( v2_pre_topc(X0)
        & ~ v2_struct_0(X0)
        & l1_pre_topc(X0) )
   => ( v2_pre_topc(sK7)
      & ~ v2_struct_0(sK7)
      & l1_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( v2_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    inference(pure_predicate_removal,[],[f35])).

fof(f35,axiom,(
    ? [X0] :
      ( v7_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0)
      & l1_pre_topc(X0) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',rc9_pre_topc)).

fof(f200,plain,(
    ~ spl8_23 ),
    inference(avatar_split_clause,[],[f114,f198])).

fof(f198,plain,
    ( spl8_23
  <=> ~ v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f114,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f74])).

fof(f193,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f113,f191])).

fof(f113,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f74])).

fof(f186,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f112,f184])).

fof(f112,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f71])).

fof(f71,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK6) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',existence_l1_pre_topc)).

fof(f179,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f111,f177])).

fof(f111,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f69])).

fof(f69,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK5) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t25_compts_1.p',existence_l1_struct_0)).

fof(f172,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f84,f170])).

fof(f84,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f165,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f83,f163])).

fof(f83,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f158,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f80,f156])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f151,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f79,f149])).

fof(f79,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f144,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f78,f142])).

fof(f78,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f137,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f77,f135])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f130,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f76,f128])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f123,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f75,f121])).

fof(f121,plain,
    ( spl8_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
