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
% DateTime   : Thu Dec  3 13:19:50 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  339 (1191 expanded)
%              Number of leaves         :   61 ( 536 expanded)
%              Depth                    :   21
%              Number of atoms          : 2627 (14337 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   31 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f150,f155,f160,f165,f170,f175,f184,f186,f193,f233,f330,f382,f408,f418,f451,f456,f461,f466,f471,f476,f481,f486,f491,f496,f501,f631,f643,f648,f663,f722,f727,f744,f749,f754,f759,f764,f779,f784,f789,f794,f804,f809,f911,f916,f1073,f1101])).

fof(f1101,plain,
    ( ~ spl11_9
    | spl11_21
    | ~ spl11_24
    | ~ spl11_42
    | spl11_44
    | ~ spl11_46
    | ~ spl11_47
    | ~ spl11_50
    | ~ spl11_51
    | ~ spl11_52
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(avatar_contradiction_clause,[],[f1100])).

fof(f1100,plain,
    ( $false
    | ~ spl11_9
    | spl11_21
    | ~ spl11_24
    | ~ spl11_42
    | spl11_44
    | ~ spl11_46
    | ~ spl11_47
    | ~ spl11_50
    | ~ spl11_51
    | ~ spl11_52
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1099,f183])).

fof(f183,plain,
    ( sP0(sK8,sK7,sK6)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl11_9
  <=> sP0(sK8,sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f1099,plain,
    ( ~ sP0(sK8,sK7,sK6)
    | spl11_21
    | ~ spl11_24
    | ~ spl11_42
    | spl11_44
    | ~ spl11_46
    | ~ spl11_47
    | ~ spl11_50
    | ~ spl11_51
    | ~ spl11_52
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1098,f381])).

fof(f381,plain,
    ( ~ v2_struct_0(sK9(sK8,sK7,sK6))
    | spl11_21 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl11_21
  <=> v2_struct_0(sK9(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f1098,plain,
    ( v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | ~ spl11_24
    | ~ spl11_42
    | spl11_44
    | ~ spl11_46
    | ~ spl11_47
    | ~ spl11_50
    | ~ spl11_51
    | ~ spl11_52
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1097,f407])).

fof(f407,plain,
    ( v2_pre_topc(sK9(sK8,sK7,sK6))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl11_24
  <=> v2_pre_topc(sK9(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f1097,plain,
    ( ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | ~ spl11_42
    | spl11_44
    | ~ spl11_46
    | ~ spl11_47
    | ~ spl11_50
    | ~ spl11_51
    | ~ spl11_52
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1096,f721])).

fof(f721,plain,
    ( l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f719])).

fof(f719,plain,
    ( spl11_42
  <=> l1_pre_topc(sK9(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f1096,plain,
    ( ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | spl11_44
    | ~ spl11_46
    | ~ spl11_47
    | ~ spl11_50
    | ~ spl11_51
    | ~ spl11_52
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1095,f753])).

fof(f753,plain,
    ( v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f751])).

fof(f751,plain,
    ( spl11_46
  <=> v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f1095,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | spl11_44
    | ~ spl11_47
    | ~ spl11_50
    | ~ spl11_51
    | ~ spl11_52
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1094,f788])).

fof(f788,plain,
    ( v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl11_52
  <=> v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f1094,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | spl11_44
    | ~ spl11_47
    | ~ spl11_50
    | ~ spl11_51
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1093,f778])).

fof(f778,plain,
    ( v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f776])).

fof(f776,plain,
    ( spl11_50
  <=> v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f1093,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | spl11_44
    | ~ spl11_47
    | ~ spl11_51
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1092,f803])).

fof(f803,plain,
    ( m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ spl11_55 ),
    inference(avatar_component_clause,[],[f801])).

fof(f801,plain,
    ( spl11_55
  <=> m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).

fof(f1092,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | spl11_44
    | ~ spl11_47
    | ~ spl11_51
    | ~ spl11_53
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1091,f758])).

fof(f758,plain,
    ( v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f756])).

fof(f756,plain,
    ( spl11_47
  <=> v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f1091,plain,
    ( ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | spl11_44
    | ~ spl11_51
    | ~ spl11_53
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1090,f793])).

fof(f793,plain,
    ( v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ spl11_53 ),
    inference(avatar_component_clause,[],[f791])).

fof(f791,plain,
    ( spl11_53
  <=> v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).

fof(f1090,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | spl11_44
    | ~ spl11_51
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1089,f783])).

fof(f783,plain,
    ( v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ spl11_51 ),
    inference(avatar_component_clause,[],[f781])).

fof(f781,plain,
    ( spl11_51
  <=> v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f1089,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | spl11_44
    | ~ spl11_56
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1088,f808])).

fof(f808,plain,
    ( m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ spl11_56 ),
    inference(avatar_component_clause,[],[f806])).

fof(f806,plain,
    ( spl11_56
  <=> m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f1088,plain,
    ( ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | spl11_44
    | ~ spl11_77 ),
    inference(subsumption_resolution,[],[f1075,f743])).

fof(f743,plain,
    ( ~ v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | spl11_44 ),
    inference(avatar_component_clause,[],[f741])).

fof(f741,plain,
    ( spl11_44
  <=> v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f1075,plain,
    ( v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ v2_pre_topc(sK9(sK8,sK7,sK6))
    | v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ sP0(sK8,sK7,sK6)
    | ~ spl11_77 ),
    inference(superposition,[],[f56,f1072])).

fof(f1072,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ spl11_77 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1070,plain,
    ( spl11_77
  <=> sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_77])])).

fof(f56,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6))))
      | ~ v5_pre_topc(X8,X0,X6)
      | ~ v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
      | ~ v5_pre_topc(X7,X1,X6)
      | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
            | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
            | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
            | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2))) )
          & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
          & v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2))
          & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
          & v1_funct_1(sK5(X0,X1,X2))
          & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
          & v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2))
          & v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
          & v1_funct_1(sK4(X0,X1,X2))
          & l1_pre_topc(sK3(X0,X1,X2))
          & v2_pre_topc(sK3(X0,X1,X2))
          & ~ v2_struct_0(sK3(X0,X1,X2)) )
        | ~ r1_tsep_1(X1,X0) )
      & ( ( ! [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( ( m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))))
                        & v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6)
                        & v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))
                        & v1_funct_1(k10_tmap_1(X2,X6,X1,X0,X7,X8)) )
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6))))
                      | ~ v5_pre_topc(X8,X0,X6)
                      | ~ v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6))
                      | ~ v1_funct_1(X8) )
                  | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                  | ~ v5_pre_topc(X7,X1,X6)
                  | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                  | ~ v1_funct_1(X7) )
              | ~ l1_pre_topc(X6)
              | ~ v2_pre_topc(X6)
              | v2_struct_0(X6) )
          & r1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                    | ~ v5_pre_topc(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),X3)
                    | ~ v1_funct_2(k10_tmap_1(X2,X3,X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                    | ~ v1_funct_1(k10_tmap_1(X2,X3,X1,X0,X4,X5)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                  & v5_pre_topc(X5,X0,X3)
                  & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X3))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(X4,X1,X3)
              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
                  | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
                  | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
                  | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
                & v5_pre_topc(X5,X0,sK3(X0,X1,X2))
                & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
            & v5_pre_topc(X4,X1,sK3(X0,X1,X2))
            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK3(X0,X1,X2))
        & v2_pre_topc(sK3(X0,X1,X2))
        & ~ v2_struct_0(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
                | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
                | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
                | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
              & v5_pre_topc(X5,X0,sK3(X0,X1,X2))
              & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
          & v5_pre_topc(X4,X1,sK3(X0,X1,X2))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
              | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
              | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
              | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
            & v5_pre_topc(X5,X0,sK3(X0,X1,X2))
            & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
            & v1_funct_1(X5) )
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
        & v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2))
        & v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
        & v1_funct_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
            | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
            | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
            | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
          & v5_pre_topc(X5,X0,sK3(X0,X1,X2))
          & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
          | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
          | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
          | ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2))) )
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
        & v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2))
        & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
        & v1_funct_1(sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                      | ~ v5_pre_topc(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),X3)
                      | ~ v1_funct_2(k10_tmap_1(X2,X3,X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                      | ~ v1_funct_1(k10_tmap_1(X2,X3,X1,X0,X4,X5)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                    & v5_pre_topc(X5,X0,X3)
                    & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(X4,X1,X3)
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X0) )
      & ( ( ! [X6] :
              ( ! [X7] :
                  ( ! [X8] :
                      ( ( m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))))
                        & v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6)
                        & v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6))
                        & v1_funct_1(k10_tmap_1(X2,X6,X1,X0,X7,X8)) )
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6))))
                      | ~ v5_pre_topc(X8,X0,X6)
                      | ~ v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6))
                      | ~ v1_funct_1(X8) )
                  | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6))))
                  | ~ v5_pre_topc(X7,X1,X6)
                  | ~ v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6))
                  | ~ v1_funct_1(X7) )
              | ~ l1_pre_topc(X6)
              | ~ v2_pre_topc(X6)
              | v2_struct_0(X6) )
          & r1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                      | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                      | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    & v5_pre_topc(X5,X2,X3)
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(X4,X1,X3)
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                        & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                        & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                        & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      | ~ v5_pre_topc(X5,X2,X3)
                      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      | ~ v1_funct_1(X5) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,X1,X3)
                  | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                      | ~ v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                      | ~ v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    & v5_pre_topc(X5,X2,X3)
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(X4,X1,X3)
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( ! [X5] :
                      ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                        & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                        & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                        & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                      | ~ v5_pre_topc(X5,X2,X3)
                      | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                      | ~ v1_funct_1(X5) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,X1,X3)
                  | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                      & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                      & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                      & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                    | ~ v5_pre_topc(X5,X2,X3)
                    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                | ~ v5_pre_topc(X4,X1,X3)
                | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
            | ~ l1_pre_topc(X3)
            | ~ v2_pre_topc(X3)
            | v2_struct_0(X3) )
        & r1_tsep_1(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1073,plain,
    ( spl11_77
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_10
    | spl11_21
    | ~ spl11_24
    | ~ spl11_42
    | ~ spl11_43
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_47
    | ~ spl11_48
    | ~ spl11_52
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_65
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f921,f913,f908,f806,f801,f791,f786,f761,f756,f751,f746,f724,f719,f405,f379,f190,f172,f167,f162,f157,f152,f147,f142,f1070])).

fof(f142,plain,
    ( spl11_1
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f147,plain,
    ( spl11_2
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f152,plain,
    ( spl11_3
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f157,plain,
    ( spl11_4
  <=> v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f162,plain,
    ( spl11_5
  <=> v2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f167,plain,
    ( spl11_6
  <=> m1_pre_topc(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f172,plain,
    ( spl11_7
  <=> m1_pre_topc(sK8,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f190,plain,
    ( spl11_10
  <=> r1_tsep_1(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f724,plain,
    ( spl11_43
  <=> v1_funct_1(sK10(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f746,plain,
    ( spl11_45
  <=> v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f761,plain,
    ( spl11_48
  <=> m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f908,plain,
    ( spl11_65
  <=> r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).

fof(f913,plain,
    ( spl11_66
  <=> r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f921,plain,
    ( sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_10
    | spl11_21
    | ~ spl11_24
    | ~ spl11_42
    | ~ spl11_43
    | ~ spl11_45
    | ~ spl11_46
    | ~ spl11_47
    | ~ spl11_48
    | ~ spl11_52
    | ~ spl11_53
    | ~ spl11_55
    | ~ spl11_56
    | ~ spl11_65
    | ~ spl11_66 ),
    inference(unit_resulting_resolution,[],[f144,f149,f154,f174,f169,f381,f407,f721,f726,f748,f753,f758,f763,f788,f793,f803,f910,f808,f915,f672])).

fof(f672,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_pre_topc(sK8,X1)
        | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK7,X2),X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | k10_tmap_1(X1,X0,sK7,sK8,X4,X3) = X2
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0))))
        | ~ v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X0))
        | ~ v1_funct_1(X4)
        | ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK8,X2),X3)
        | ~ m1_pre_topc(sK7,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl11_4
    | spl11_5
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f671,f159])).

fof(f159,plain,
    ( ~ v2_struct_0(sK7)
    | spl11_4 ),
    inference(avatar_component_clause,[],[f157])).

fof(f671,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK8,X2),X3)
        | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK7,X2),X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | k10_tmap_1(X1,X0,sK7,sK8,X4,X3) = X2
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0))))
        | ~ v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X0))
        | ~ v1_funct_1(X4)
        | ~ m1_pre_topc(sK8,X1)
        | ~ m1_pre_topc(sK7,X1)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | spl11_5
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f668,f164])).

fof(f164,plain,
    ( ~ v2_struct_0(sK8)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f162])).

fof(f668,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK8),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK8,X2),X3)
        | ~ r2_funct_2(u1_struct_0(sK7),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK7,X2),X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | k10_tmap_1(X1,X0,sK7,sK8,X4,X3) = X2
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0))))
        | ~ v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X0))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0))))
        | ~ v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X0))
        | ~ v1_funct_1(X4)
        | ~ m1_pre_topc(sK8,X1)
        | v2_struct_0(sK8)
        | ~ m1_pre_topc(sK7,X1)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl11_10 ),
    inference(resolution,[],[f192,f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X6)
      | k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) )
                                  | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                  & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(X6) )
                          | ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & ~ r1_tsep_1(X2,X3) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | r1_tsep_1(X2,X3) )
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(X6) )
                               => ( k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5)
                                    & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_tmap_1)).

fof(f192,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f190])).

fof(f915,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ spl11_66 ),
    inference(avatar_component_clause,[],[f913])).

fof(f910,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ spl11_65 ),
    inference(avatar_component_clause,[],[f908])).

fof(f763,plain,
    ( m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f761])).

fof(f748,plain,
    ( v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f746])).

fof(f726,plain,
    ( v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ spl11_43 ),
    inference(avatar_component_clause,[],[f724])).

fof(f169,plain,
    ( m1_pre_topc(sK7,sK6)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f174,plain,
    ( m1_pre_topc(sK8,sK6)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f154,plain,
    ( l1_pre_topc(sK6)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f152])).

fof(f149,plain,
    ( v2_pre_topc(sK6)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f144,plain,
    ( ~ v2_struct_0(sK6)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f142])).

fof(f916,plain,
    ( spl11_66
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f705,f327,f190,f913])).

fof(f327,plain,
    ( spl11_16
  <=> sP1(sK8,sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f705,plain,
    ( r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f236])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))
      | ~ r1_tsep_1(X1,X0)
      | sP1(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f235,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
            | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
            | ~ v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
            | ~ v1_funct_1(sK10(X0,X1,X2)) )
          & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))
          & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))
          & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
          & v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(sK10(X0,X1,X2))
          & l1_pre_topc(sK9(X0,X1,X2))
          & v2_pre_topc(sK9(X0,X1,X2))
          & ~ v2_struct_0(sK9(X0,X1,X2)) )
        | ~ r1_tsep_1(X1,X0) )
      & ( ( ! [X5] :
              ( ! [X6] :
                  ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))))
                    & v5_pre_topc(X6,k1_tsep_1(X2,X1,X0),X5)
                    & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))
                    & v1_funct_1(X6) )
                  | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                  | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),X0,X5)
                  | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),u1_struct_0(X0),u1_struct_0(X5))
                  | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6))
                  | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                  | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),X1,X5)
                  | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),u1_struct_0(X1),u1_struct_0(X5))
                  | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6))
                  | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))))
                  | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))
                  | ~ v1_funct_1(X6) )
              | ~ l1_pre_topc(X5)
              | ~ v2_pre_topc(X5)
              | v2_struct_0(X5) )
          & r1_tsep_1(X1,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f46,f48,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                | ~ v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),X3)
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
              & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
              & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),X0,X3)
              & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(X3))
              & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4))
              & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
              & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),X1,X3)
              & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
              & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
              & v1_funct_1(X4) )
          & l1_pre_topc(X3)
          & v2_pre_topc(X3)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
              | ~ v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
              | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
              | ~ v1_funct_1(X4) )
            & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
            & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),X0,sK9(X0,X1,X2))
            & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
            & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4))
            & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
            & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),X1,sK9(X0,X1,X2))
            & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
            & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
            & v1_funct_1(X4) )
        & l1_pre_topc(sK9(X0,X1,X2))
        & v2_pre_topc(sK9(X0,X1,X2))
        & ~ v2_struct_0(sK9(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
            | ~ v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
            | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
            | ~ v1_funct_1(X4) )
          & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),X0,sK9(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4))
          & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
          & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),X1,sK9(X0,X1,X2))
          & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
          & v1_funct_1(X4) )
     => ( ( ~ m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
          | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
          | ~ v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
          | ~ v1_funct_1(sK10(X0,X1,X2)) )
        & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
        & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2))
        & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
        & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))
        & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
        & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2))
        & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
        & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
        & v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
        & v1_funct_1(sK10(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),X3)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
                & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),X0,X3)
                & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4))
                & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),X1,X3)
                & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X0) )
      & ( ( ! [X5] :
              ( ! [X6] :
                  ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))))
                    & v5_pre_topc(X6,k1_tsep_1(X2,X1,X0),X5)
                    & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))
                    & v1_funct_1(X6) )
                  | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5))))
                  | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),X0,X5)
                  | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),u1_struct_0(X0),u1_struct_0(X5))
                  | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6))
                  | ~ m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5))))
                  | ~ v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),X1,X5)
                  | ~ v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),u1_struct_0(X1),u1_struct_0(X5))
                  | ~ v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6))
                  | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))))
                  | ~ v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5))
                  | ~ v1_funct_1(X6) )
              | ~ l1_pre_topc(X5)
              | ~ v2_pre_topc(X5)
              | v2_struct_0(X5) )
          & r1_tsep_1(X1,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
                & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                    & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                    & v1_funct_1(X4) )
                  | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                  | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                  | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                  | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                  | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ( sP1(X2,X1,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  | ~ v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
                & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                & v1_funct_1(X4) )
            & l1_pre_topc(X3)
            & v2_pre_topc(X3)
            & ~ v2_struct_0(X3) )
        | ~ r1_tsep_1(X1,X2) )
      & ( ( ! [X3] :
              ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                    & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                    & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                    & v1_funct_1(X4) )
                  | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                  | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                  | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                  | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                  | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                  | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                  | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  | ~ v1_funct_1(X4) )
              | ~ l1_pre_topc(X3)
              | ~ v2_pre_topc(X3)
              | v2_struct_0(X3) )
          & r1_tsep_1(X1,X2) )
        | ~ sP1(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( sP1(X2,X1,X0)
    <=> ( ! [X3] :
            ( ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                  & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                  & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                  & v1_funct_1(X4) )
                | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                | ~ v1_funct_1(X4) )
            | ~ l1_pre_topc(X3)
            | ~ v2_pre_topc(X3)
            | v2_struct_0(X3) )
        & r1_tsep_1(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))
      | ~ v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f234,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0)
      | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))
      | ~ v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))
      | ~ v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) ) ),
    inference(resolution,[],[f109,f125])).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)))))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f329,plain,
    ( ~ sP1(sK8,sK7,sK6)
    | spl11_16 ),
    inference(avatar_component_clause,[],[f327])).

fof(f911,plain,
    ( spl11_65
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f704,f327,f190,f908])).

fof(f704,plain,
    ( r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f228])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))
      | ~ r1_tsep_1(X1,X0)
      | sP1(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f227,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0)
      | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))
      | ~ v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f226,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0)
      | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))
      | ~ v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))
      | ~ v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) ) ),
    inference(resolution,[],[f105,f125])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)))))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f809,plain,
    ( spl11_56
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f701,f327,f190,f806])).

fof(f701,plain,
    ( m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f109])).

fof(f804,plain,
    ( spl11_55
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f697,f327,f190,f801])).

fof(f697,plain,
    ( m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f105])).

fof(f794,plain,
    ( spl11_53
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f699,f327,f190,f791])).

fof(f699,plain,
    ( v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f107])).

fof(f789,plain,
    ( spl11_52
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f695,f327,f190,f786])).

fof(f695,plain,
    ( v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f103])).

fof(f784,plain,
    ( spl11_51
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f700,f327,f190,f781])).

fof(f700,plain,
    ( v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f779,plain,
    ( spl11_50
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f696,f327,f190,f776])).

fof(f696,plain,
    ( v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f764,plain,
    ( spl11_48
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f693,f327,f190,f761])).

fof(f693,plain,
    ( m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f759,plain,
    ( spl11_47
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f698,f327,f190,f756])).

fof(f698,plain,
    ( v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f106])).

fof(f754,plain,
    ( spl11_46
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f694,f327,f190,f751])).

fof(f694,plain,
    ( v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f102])).

fof(f749,plain,
    ( spl11_45
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f692,f327,f190,f746])).

fof(f692,plain,
    ( v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f744,plain,
    ( ~ spl11_44
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f702,f327,f190,f741])).

fof(f702,plain,
    ( ~ v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f127,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK10(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
      | ~ v1_funct_1(sK10(X0,X1,X2))
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f126,f100])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
      | ~ v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
      | ~ v1_funct_1(sK10(X0,X1,X2))
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f110,f101])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))))
      | ~ v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2))
      | ~ v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2)))
      | ~ v1_funct_1(sK10(X0,X1,X2))
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f727,plain,
    ( spl11_43
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f691,f327,f190,f724])).

fof(f691,plain,
    ( v1_funct_1(sK10(sK8,sK7,sK6))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f99])).

fof(f722,plain,
    ( spl11_42
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f690,f327,f190,f719])).

fof(f690,plain,
    ( l1_pre_topc(sK9(sK8,sK7,sK6))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f663,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_16 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8
    | spl11_16 ),
    inference(subsumption_resolution,[],[f329,f661])).

fof(f661,plain,
    ( sP1(sK8,sK7,sK6)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f660,f164])).

fof(f660,plain,
    ( v2_struct_0(sK8)
    | sP1(sK8,sK7,sK6)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f425,f174])).

fof(f425,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | sP1(sK8,sK7,sK6)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | ~ spl11_6
    | ~ spl11_8 ),
    inference(resolution,[],[f179,f285])).

fof(f285,plain,
    ( ! [X1] :
        ( ~ r3_tsep_1(sK6,sK7,X1)
        | ~ m1_pre_topc(X1,sK6)
        | v2_struct_0(X1)
        | sP1(X1,sK7,sK6) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | ~ spl11_6 ),
    inference(resolution,[],[f203,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | sP1(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_tsep_1(X0,X1,X2)
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r3_tsep_1(X0,X1,X2) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_tsep_1(X0,X1,X2)
      <=> sP1(X2,X1,X0) )
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f203,plain,
    ( ! [X0] :
        ( sP2(sK6,sK7,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK6) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f202,f144])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK6)
        | v2_struct_0(X0)
        | sP2(sK6,sK7,X0)
        | v2_struct_0(sK6) )
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f201,f149])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK6)
        | v2_struct_0(X0)
        | sP2(sK6,sK7,X0)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | ~ spl11_3
    | spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f200,f154])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK6)
        | v2_struct_0(X0)
        | sP2(sK6,sK7,X0)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f198,f159])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK6)
        | v2_struct_0(X0)
        | sP2(sK6,sK7,X0)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | ~ spl11_6 ),
    inference(resolution,[],[f111,f169])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | sP2(X0,X1,X2)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f16,f26,f25])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                          | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                          | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ( ( m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
                              & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
                              & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) )
                           => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                              & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
                              & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                              & v1_funct_1(X4) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_tmap_1)).

fof(f179,plain,
    ( r3_tsep_1(sK6,sK7,sK8)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl11_8
  <=> r3_tsep_1(sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f648,plain,
    ( spl11_10
    | ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f647])).

fof(f647,plain,
    ( $false
    | spl11_10
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f191,f446])).

fof(f446,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ spl11_16 ),
    inference(resolution,[],[f328,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f328,plain,
    ( sP1(sK8,sK7,sK6)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f327])).

fof(f191,plain,
    ( ~ r1_tsep_1(sK7,sK8)
    | spl11_10 ),
    inference(avatar_component_clause,[],[f190])).

fof(f643,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_9
    | ~ spl11_10
    | ~ spl11_15
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_30
    | ~ spl11_31
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35
    | ~ spl11_40 ),
    inference(avatar_contradiction_clause,[],[f642])).

fof(f642,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_9
    | ~ spl11_10
    | ~ spl11_15
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_30
    | ~ spl11_31
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f641,f192])).

fof(f641,plain,
    ( ~ r1_tsep_1(sK7,sK8)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_9
    | ~ spl11_10
    | ~ spl11_15
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_30
    | ~ spl11_31
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f640,f182])).

fof(f182,plain,
    ( ~ sP0(sK8,sK7,sK6)
    | spl11_9 ),
    inference(avatar_component_clause,[],[f181])).

fof(f640,plain,
    ( sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_10
    | ~ spl11_15
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_30
    | ~ spl11_31
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f639,f526])).

fof(f526,plain,
    ( v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35 ),
    inference(unit_resulting_resolution,[],[f144,f149,f154,f164,f169,f174,f159,f450,f455,f460,f465,f470,f485,f495,f490,f500,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f500,plain,
    ( m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ spl11_35 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl11_35
  <=> m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).

fof(f490,plain,
    ( v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f488])).

fof(f488,plain,
    ( spl11_33
  <=> v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f495,plain,
    ( m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl11_34
  <=> m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f485,plain,
    ( v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f483])).

fof(f483,plain,
    ( spl11_32
  <=> v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f470,plain,
    ( v1_funct_1(sK5(sK8,sK7,sK6))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl11_29
  <=> v1_funct_1(sK5(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f465,plain,
    ( v1_funct_1(sK4(sK8,sK7,sK6))
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl11_28
  <=> v1_funct_1(sK4(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f460,plain,
    ( l1_pre_topc(sK3(sK8,sK7,sK6))
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl11_27
  <=> l1_pre_topc(sK3(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f455,plain,
    ( v2_pre_topc(sK3(sK8,sK7,sK6))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl11_26
  <=> v2_pre_topc(sK3(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f450,plain,
    ( ~ v2_struct_0(sK3(sK8,sK7,sK6))
    | spl11_25 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl11_25
  <=> v2_struct_0(sK3(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f639,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_10
    | ~ spl11_15
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_30
    | ~ spl11_31
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f638,f518])).

fof(f518,plain,
    ( v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_10
    | ~ spl11_15
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_30
    | ~ spl11_31
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35 ),
    inference(unit_resulting_resolution,[],[f144,f149,f154,f164,f159,f174,f192,f169,f315,f450,f455,f460,f465,f470,f475,f485,f495,f480,f490,f500,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

% (16332)Refutation not found, incomplete strategy% (16332)------------------------------
% (16332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16332)Termination reason: Refutation not found, incomplete strategy

% (16332)Memory used [KB]: 6140
% (16332)Time elapsed: 0.185 s
% (16332)------------------------------
% (16332)------------------------------
fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_tmap_1)).

fof(f480,plain,
    ( v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f478])).

fof(f478,plain,
    ( spl11_31
  <=> v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f475,plain,
    ( v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl11_30
  <=> v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f315,plain,
    ( r4_tsep_1(sK6,sK7,sK8)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl11_15
  <=> r4_tsep_1(sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f638,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35
    | ~ spl11_40 ),
    inference(subsumption_resolution,[],[f637,f530])).

fof(f530,plain,
    ( m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35 ),
    inference(unit_resulting_resolution,[],[f144,f149,f154,f164,f169,f174,f159,f450,f455,f460,f465,f470,f485,f495,f490,f500,f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f637,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | ~ v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6))
    | ~ v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6)))
    | sP0(sK8,sK7,sK6)
    | ~ r1_tsep_1(sK7,sK8)
    | ~ spl11_40 ),
    inference(resolution,[],[f630,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)))
      | ~ m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))))
      | ~ v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2))
      | ~ v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2)))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f630,plain,
    ( v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)))
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f628])).

fof(f628,plain,
    ( spl11_40
  <=> v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f631,plain,
    ( spl11_40
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35 ),
    inference(avatar_split_clause,[],[f534,f498,f493,f488,f483,f468,f463,f458,f453,f448,f172,f167,f162,f157,f152,f147,f142,f628])).

fof(f534,plain,
    ( v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_25
    | ~ spl11_26
    | ~ spl11_27
    | ~ spl11_28
    | ~ spl11_29
    | ~ spl11_32
    | ~ spl11_33
    | ~ spl11_34
    | ~ spl11_35 ),
    inference(unit_resulting_resolution,[],[f164,f174,f450,f455,f460,f470,f465,f485,f495,f490,f500,f243])).

fof(f243,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X1,sK6)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | v2_struct_0(X1)
        | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f242,f144])).

fof(f242,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X1,sK6)
        | v2_struct_0(X1)
        | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | v2_struct_0(sK6) )
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f241,f149])).

fof(f241,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X1,sK6)
        | v2_struct_0(X1)
        | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | ~ spl11_3
    | spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f240,f154])).

fof(f240,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X1,sK6)
        | v2_struct_0(X1)
        | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f238,f159])).

fof(f238,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2))
        | ~ v1_funct_1(X3)
        | ~ m1_pre_topc(X1,sK6)
        | v2_struct_0(X1)
        | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0))
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | ~ spl11_6 ),
    inference(resolution,[],[f117,f169])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f501,plain,
    ( spl11_35
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f437,f190,f181,f498])).

fof(f437,plain,
    ( m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f496,plain,
    ( spl11_34
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f433,f190,f181,f493])).

fof(f433,plain,
    ( m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f491,plain,
    ( spl11_33
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f435,f190,f181,f488])).

fof(f435,plain,
    ( v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2)))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f486,plain,
    ( spl11_32
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f431,f190,f181,f483])).

fof(f431,plain,
    ( v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2)))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f481,plain,
    ( spl11_31
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f436,f190,f181,f478])).

fof(f436,plain,
    ( v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f476,plain,
    ( spl11_30
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f432,f190,f181,f473])).

fof(f432,plain,
    ( v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f471,plain,
    ( spl11_29
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f434,f190,f181,f468])).

fof(f434,plain,
    ( v1_funct_1(sK5(sK8,sK7,sK6))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK5(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f466,plain,
    ( spl11_28
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f430,f190,f181,f463])).

fof(f430,plain,
    ( v1_funct_1(sK4(sK8,sK7,sK6))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK4(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f461,plain,
    ( spl11_27
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f429,f190,f181,f458])).

fof(f429,plain,
    ( l1_pre_topc(sK3(sK8,sK7,sK6))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f456,plain,
    ( spl11_26
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f428,f190,f181,f453])).

fof(f428,plain,
    ( v2_pre_topc(sK3(sK8,sK7,sK6))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f451,plain,
    ( ~ spl11_25
    | spl11_9
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f427,f190,f181,f448])).

fof(f427,plain,
    ( ~ v2_struct_0(sK3(sK8,sK7,sK6))
    | spl11_9
    | ~ spl11_10 ),
    inference(unit_resulting_resolution,[],[f192,f182,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1,X2))
      | sP0(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f418,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_12
    | spl11_15
    | ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_12
    | spl11_15
    | ~ spl11_16 ),
    inference(subsumption_resolution,[],[f328,f416])).

fof(f416,plain,
    ( ~ sP1(sK8,sK7,sK6)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_12
    | spl11_15 ),
    inference(subsumption_resolution,[],[f276,f415])).

fof(f415,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f414,f144])).

fof(f414,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | v2_struct_0(sK6)
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f413,f149])).

fof(f413,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f412,f154])).

fof(f412,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f411,f159])).

fof(f411,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f410,f169])).

fof(f410,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl11_5
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f409,f164])).

fof(f409,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ spl11_7
    | spl11_15 ),
    inference(subsumption_resolution,[],[f332,f174])).

fof(f332,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | spl11_15 ),
    inference(resolution,[],[f316,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ r3_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r4_tsep_1(X0,X1,X2)
                    & r1_tsep_1(X1,X2) )
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( r3_tsep_1(X0,X1,X2)
                  | ~ r4_tsep_1(X0,X1,X2)
                  | ~ r1_tsep_1(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ( r4_tsep_1(X0,X1,X2)
                  & r1_tsep_1(X1,X2) )
              <=> r3_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tsep_1)).

fof(f316,plain,
    ( ~ r4_tsep_1(sK6,sK7,sK8)
    | spl11_15 ),
    inference(avatar_component_clause,[],[f314])).

fof(f276,plain,
    ( ~ sP1(sK8,sK7,sK6)
    | r3_tsep_1(sK6,sK7,sK8)
    | ~ spl11_12 ),
    inference(resolution,[],[f232,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X2,X1,X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

% (16343)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f232,plain,
    ( sP2(sK6,sK7,sK8)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl11_12
  <=> sP2(sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f408,plain,
    ( spl11_24
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f335,f327,f190,f405])).

fof(f335,plain,
    ( v2_pre_topc(sK9(sK8,sK7,sK6))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f382,plain,
    ( ~ spl11_21
    | ~ spl11_10
    | spl11_16 ),
    inference(avatar_split_clause,[],[f334,f327,f190,f379])).

fof(f334,plain,
    ( ~ v2_struct_0(sK9(sK8,sK7,sK6))
    | ~ spl11_10
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f192,f329,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK9(X0,X1,X2))
      | sP1(X0,X1,X2)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f330,plain,
    ( ~ spl11_16
    | spl11_8
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f275,f230,f177,f327])).

fof(f275,plain,
    ( ~ sP1(sK8,sK7,sK6)
    | spl11_8
    | ~ spl11_12 ),
    inference(unit_resulting_resolution,[],[f178,f232,f90])).

fof(f178,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | spl11_8 ),
    inference(avatar_component_clause,[],[f177])).

fof(f233,plain,
    ( spl11_12
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f195,f172,f167,f162,f157,f152,f147,f142,f230])).

fof(f195,plain,
    ( sP2(sK6,sK7,sK8)
    | spl11_1
    | ~ spl11_2
    | ~ spl11_3
    | spl11_4
    | spl11_5
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(unit_resulting_resolution,[],[f144,f149,f154,f159,f164,f174,f169,f111])).

fof(f193,plain,
    ( spl11_10
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f187,f181,f190])).

fof(f187,plain,
    ( r1_tsep_1(sK7,sK8)
    | ~ spl11_9 ),
    inference(unit_resulting_resolution,[],[f183,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f186,plain,
    ( ~ spl11_8
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f185,f181,f177])).

fof(f185,plain,
    ( ~ r3_tsep_1(sK6,sK7,sK8)
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f78,f183])).

fof(f78,plain,
    ( ~ sP0(sK8,sK7,sK6)
    | ~ r3_tsep_1(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ sP0(sK8,sK7,sK6)
      | ~ r3_tsep_1(sK6,sK7,sK8) )
    & ( sP0(sK8,sK7,sK6)
      | r3_tsep_1(sK6,sK7,sK8) )
    & m1_pre_topc(sK8,sK6)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK6)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ sP0(X2,X1,X0)
                  | ~ r3_tsep_1(X0,X1,X2) )
                & ( sP0(X2,X1,X0)
                  | r3_tsep_1(X0,X1,X2) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP0(X2,X1,sK6)
                | ~ r3_tsep_1(sK6,X1,X2) )
              & ( sP0(X2,X1,sK6)
                | r3_tsep_1(sK6,X1,X2) )
              & m1_pre_topc(X2,sK6)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK6)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ sP0(X2,X1,sK6)
              | ~ r3_tsep_1(sK6,X1,X2) )
            & ( sP0(X2,X1,sK6)
              | r3_tsep_1(sK6,X1,X2) )
            & m1_pre_topc(X2,sK6)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK6)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ sP0(X2,sK7,sK6)
            | ~ r3_tsep_1(sK6,sK7,X2) )
          & ( sP0(X2,sK7,sK6)
            | r3_tsep_1(sK6,sK7,X2) )
          & m1_pre_topc(X2,sK6)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK7,sK6)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ( ~ sP0(X2,sK7,sK6)
          | ~ r3_tsep_1(sK6,sK7,X2) )
        & ( sP0(X2,sK7,sK6)
          | r3_tsep_1(sK6,sK7,X2) )
        & m1_pre_topc(X2,sK6)
        & ~ v2_struct_0(X2) )
   => ( ( ~ sP0(sK8,sK7,sK6)
        | ~ r3_tsep_1(sK6,sK7,sK8) )
      & ( sP0(sK8,sK7,sK6)
        | r3_tsep_1(sK6,sK7,sK8) )
      & m1_pre_topc(sK8,sK6)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP0(X2,X1,X0)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( sP0(X2,X1,X0)
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP0(X2,X1,X0)
                | ~ r3_tsep_1(X0,X1,X2) )
              & ( sP0(X2,X1,X0)
                | r3_tsep_1(X0,X1,X2) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> sP0(X2,X1,X0) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f10,f23])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ! [X5] :
                              ( ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) )
                              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                              | ~ v5_pre_topc(X5,X2,X3)
                              | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                              | ~ v1_funct_1(X5) )
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(X4,X1,X3)
                          | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                              & v5_pre_topc(X4,X1,X3)
                              & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(X5,X2,X3)
                                  & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(X5) )
                               => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                  & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                  & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                  & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r3_tsep_1(X0,X1,X2)
              <=> ( ! [X3] :
                      ( ( l1_pre_topc(X3)
                        & v2_pre_topc(X3)
                        & ~ v2_struct_0(X3) )
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X1,X3)
                            & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(X5,X2,X3)
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(X5) )
                             => ( m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
                                & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3)
                                & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
                                & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)) ) ) ) )
                  & r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_tmap_1)).

fof(f184,plain,
    ( spl11_8
    | spl11_9 ),
    inference(avatar_split_clause,[],[f77,f181,f177])).

fof(f77,plain,
    ( sP0(sK8,sK7,sK6)
    | r3_tsep_1(sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f175,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f76,f172])).

fof(f76,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f170,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f74,f167])).

fof(f74,plain,(
    m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f165,plain,(
    ~ spl11_5 ),
    inference(avatar_split_clause,[],[f75,f162])).

fof(f75,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f160,plain,(
    ~ spl11_4 ),
    inference(avatar_split_clause,[],[f73,f157])).

fof(f73,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f155,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f72,f152])).

fof(f72,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f150,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f71,f147])).

fof(f71,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f145,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f70,f142])).

fof(f70,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:08:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (16346)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.48  % (16330)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (16330)Refutation not found, incomplete strategy% (16330)------------------------------
% 0.21/0.49  % (16330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16332)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.49  % (16330)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (16330)Memory used [KB]: 1918
% 0.21/0.49  % (16330)Time elapsed: 0.068 s
% 0.21/0.49  % (16330)------------------------------
% 0.21/0.49  % (16330)------------------------------
% 0.21/0.50  % (16335)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (16331)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (16327)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (16328)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (16324)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (16341)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (16323)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (16323)Refutation not found, incomplete strategy% (16323)------------------------------
% 0.21/0.51  % (16323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16323)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16323)Memory used [KB]: 10618
% 0.21/0.51  % (16323)Time elapsed: 0.105 s
% 0.21/0.51  % (16323)------------------------------
% 0.21/0.51  % (16323)------------------------------
% 0.21/0.52  % (16342)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (16345)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (16340)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (16334)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (16326)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (16339)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.32/0.53  % (16336)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.32/0.53  % (16344)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.32/0.53  % (16338)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.32/0.53  % (16336)Refutation not found, incomplete strategy% (16336)------------------------------
% 1.32/0.53  % (16336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (16336)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (16336)Memory used [KB]: 6268
% 1.32/0.53  % (16336)Time elapsed: 0.122 s
% 1.32/0.53  % (16336)------------------------------
% 1.32/0.53  % (16336)------------------------------
% 1.32/0.54  % (16329)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.32/0.54  % (16337)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.32/0.55  % (16347)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.32/0.55  % (16333)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.54/0.56  % (16334)Refutation not found, incomplete strategy% (16334)------------------------------
% 1.54/0.56  % (16334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (16334)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (16334)Memory used [KB]: 11129
% 1.54/0.56  % (16334)Time elapsed: 0.163 s
% 1.54/0.56  % (16334)------------------------------
% 1.54/0.56  % (16334)------------------------------
% 1.54/0.57  % (16329)Refutation not found, incomplete strategy% (16329)------------------------------
% 1.54/0.57  % (16329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (16329)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (16329)Memory used [KB]: 10746
% 1.54/0.57  % (16329)Time elapsed: 0.131 s
% 1.54/0.57  % (16329)------------------------------
% 1.54/0.57  % (16329)------------------------------
% 1.54/0.59  % (16348)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.54/0.59  % (16325)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.54/0.59  % (16346)Refutation found. Thanks to Tanya!
% 1.54/0.59  % SZS status Theorem for theBenchmark
% 1.54/0.59  % SZS output start Proof for theBenchmark
% 1.54/0.59  fof(f1102,plain,(
% 1.54/0.59    $false),
% 1.54/0.59    inference(avatar_sat_refutation,[],[f145,f150,f155,f160,f165,f170,f175,f184,f186,f193,f233,f330,f382,f408,f418,f451,f456,f461,f466,f471,f476,f481,f486,f491,f496,f501,f631,f643,f648,f663,f722,f727,f744,f749,f754,f759,f764,f779,f784,f789,f794,f804,f809,f911,f916,f1073,f1101])).
% 1.54/0.59  fof(f1101,plain,(
% 1.54/0.59    ~spl11_9 | spl11_21 | ~spl11_24 | ~spl11_42 | spl11_44 | ~spl11_46 | ~spl11_47 | ~spl11_50 | ~spl11_51 | ~spl11_52 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_77),
% 1.54/0.59    inference(avatar_contradiction_clause,[],[f1100])).
% 1.54/0.59  fof(f1100,plain,(
% 1.54/0.59    $false | (~spl11_9 | spl11_21 | ~spl11_24 | ~spl11_42 | spl11_44 | ~spl11_46 | ~spl11_47 | ~spl11_50 | ~spl11_51 | ~spl11_52 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1099,f183])).
% 1.54/0.59  fof(f183,plain,(
% 1.54/0.59    sP0(sK8,sK7,sK6) | ~spl11_9),
% 1.54/0.59    inference(avatar_component_clause,[],[f181])).
% 1.54/0.59  fof(f181,plain,(
% 1.54/0.59    spl11_9 <=> sP0(sK8,sK7,sK6)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.54/0.59  fof(f1099,plain,(
% 1.54/0.59    ~sP0(sK8,sK7,sK6) | (spl11_21 | ~spl11_24 | ~spl11_42 | spl11_44 | ~spl11_46 | ~spl11_47 | ~spl11_50 | ~spl11_51 | ~spl11_52 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1098,f381])).
% 1.54/0.59  fof(f381,plain,(
% 1.54/0.59    ~v2_struct_0(sK9(sK8,sK7,sK6)) | spl11_21),
% 1.54/0.59    inference(avatar_component_clause,[],[f379])).
% 1.54/0.59  fof(f379,plain,(
% 1.54/0.59    spl11_21 <=> v2_struct_0(sK9(sK8,sK7,sK6))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 1.54/0.59  fof(f1098,plain,(
% 1.54/0.59    v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (~spl11_24 | ~spl11_42 | spl11_44 | ~spl11_46 | ~spl11_47 | ~spl11_50 | ~spl11_51 | ~spl11_52 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1097,f407])).
% 1.54/0.59  fof(f407,plain,(
% 1.54/0.59    v2_pre_topc(sK9(sK8,sK7,sK6)) | ~spl11_24),
% 1.54/0.59    inference(avatar_component_clause,[],[f405])).
% 1.54/0.59  fof(f405,plain,(
% 1.54/0.59    spl11_24 <=> v2_pre_topc(sK9(sK8,sK7,sK6))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).
% 1.54/0.59  fof(f1097,plain,(
% 1.54/0.59    ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (~spl11_42 | spl11_44 | ~spl11_46 | ~spl11_47 | ~spl11_50 | ~spl11_51 | ~spl11_52 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1096,f721])).
% 1.54/0.59  fof(f721,plain,(
% 1.54/0.59    l1_pre_topc(sK9(sK8,sK7,sK6)) | ~spl11_42),
% 1.54/0.59    inference(avatar_component_clause,[],[f719])).
% 1.54/0.59  fof(f719,plain,(
% 1.54/0.59    spl11_42 <=> l1_pre_topc(sK9(sK8,sK7,sK6))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).
% 1.54/0.59  fof(f1096,plain,(
% 1.54/0.59    ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (spl11_44 | ~spl11_46 | ~spl11_47 | ~spl11_50 | ~spl11_51 | ~spl11_52 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1095,f753])).
% 1.54/0.59  fof(f753,plain,(
% 1.54/0.59    v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~spl11_46),
% 1.54/0.59    inference(avatar_component_clause,[],[f751])).
% 1.54/0.59  fof(f751,plain,(
% 1.54/0.59    spl11_46 <=> v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).
% 1.54/0.59  fof(f1095,plain,(
% 1.54/0.59    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (spl11_44 | ~spl11_47 | ~spl11_50 | ~spl11_51 | ~spl11_52 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1094,f788])).
% 1.54/0.59  fof(f788,plain,(
% 1.54/0.59    v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~spl11_52),
% 1.54/0.59    inference(avatar_component_clause,[],[f786])).
% 1.54/0.59  fof(f786,plain,(
% 1.54/0.59    spl11_52 <=> v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).
% 1.54/0.59  fof(f1094,plain,(
% 1.54/0.59    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (spl11_44 | ~spl11_47 | ~spl11_50 | ~spl11_51 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1093,f778])).
% 1.54/0.59  fof(f778,plain,(
% 1.54/0.59    v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~spl11_50),
% 1.54/0.59    inference(avatar_component_clause,[],[f776])).
% 1.54/0.59  fof(f776,plain,(
% 1.54/0.59    spl11_50 <=> v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).
% 1.54/0.59  fof(f1093,plain,(
% 1.54/0.59    ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (spl11_44 | ~spl11_47 | ~spl11_51 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1092,f803])).
% 1.54/0.59  fof(f803,plain,(
% 1.54/0.59    m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~spl11_55),
% 1.54/0.59    inference(avatar_component_clause,[],[f801])).
% 1.54/0.59  fof(f801,plain,(
% 1.54/0.59    spl11_55 <=> m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)))))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_55])])).
% 1.54/0.59  fof(f1092,plain,(
% 1.54/0.59    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (spl11_44 | ~spl11_47 | ~spl11_51 | ~spl11_53 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1091,f758])).
% 1.54/0.59  fof(f758,plain,(
% 1.54/0.59    v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~spl11_47),
% 1.54/0.59    inference(avatar_component_clause,[],[f756])).
% 1.54/0.59  fof(f756,plain,(
% 1.54/0.59    spl11_47 <=> v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).
% 1.54/0.59  fof(f1091,plain,(
% 1.54/0.59    ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (spl11_44 | ~spl11_51 | ~spl11_53 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1090,f793])).
% 1.54/0.59  fof(f793,plain,(
% 1.54/0.59    v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~spl11_53),
% 1.54/0.59    inference(avatar_component_clause,[],[f791])).
% 1.54/0.59  fof(f791,plain,(
% 1.54/0.59    spl11_53 <=> v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_53])])).
% 1.54/0.59  fof(f1090,plain,(
% 1.54/0.59    ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (spl11_44 | ~spl11_51 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1089,f783])).
% 1.54/0.59  fof(f783,plain,(
% 1.54/0.59    v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | ~spl11_51),
% 1.54/0.59    inference(avatar_component_clause,[],[f781])).
% 1.54/0.59  fof(f781,plain,(
% 1.54/0.59    spl11_51 <=> v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).
% 1.54/0.59  fof(f1089,plain,(
% 1.54/0.59    ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (spl11_44 | ~spl11_56 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1088,f808])).
% 1.54/0.59  fof(f808,plain,(
% 1.54/0.59    m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~spl11_56),
% 1.54/0.59    inference(avatar_component_clause,[],[f806])).
% 1.54/0.59  fof(f806,plain,(
% 1.54/0.59    spl11_56 <=> m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)))))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).
% 1.54/0.59  fof(f1088,plain,(
% 1.54/0.59    ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | (spl11_44 | ~spl11_77)),
% 1.54/0.59    inference(subsumption_resolution,[],[f1075,f743])).
% 1.54/0.59  fof(f743,plain,(
% 1.54/0.59    ~v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | spl11_44),
% 1.54/0.59    inference(avatar_component_clause,[],[f741])).
% 1.54/0.59  fof(f741,plain,(
% 1.54/0.59    spl11_44 <=> v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).
% 1.54/0.59  fof(f1075,plain,(
% 1.54/0.59    v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | ~v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | ~v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~l1_pre_topc(sK9(sK8,sK7,sK6)) | ~v2_pre_topc(sK9(sK8,sK7,sK6)) | v2_struct_0(sK9(sK8,sK7,sK6)) | ~sP0(sK8,sK7,sK6) | ~spl11_77),
% 1.54/0.59    inference(superposition,[],[f56,f1072])).
% 1.54/0.59  fof(f1072,plain,(
% 1.54/0.59    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~spl11_77),
% 1.54/0.59    inference(avatar_component_clause,[],[f1070])).
% 1.54/0.59  fof(f1070,plain,(
% 1.54/0.59    spl11_77 <=> sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl11_77])])).
% 1.54/0.60  fof(f56,plain,(
% 1.54/0.60    ( ! [X6,X2,X0,X8,X7,X1] : (v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6)))) | ~v5_pre_topc(X8,X0,X6) | ~v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6)) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6)))) | ~v5_pre_topc(X7,X1,X6) | ~v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6)) | ~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP0(X0,X1,X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f34,plain,(
% 1.54/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)))) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2)) & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(sK5(X0,X1,X2))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2)) & v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(sK4(X0,X1,X2))) & l1_pre_topc(sK3(X0,X1,X2)) & v2_pre_topc(sK3(X0,X1,X2)) & ~v2_struct_0(sK3(X0,X1,X2))) | ~r1_tsep_1(X1,X0)) & ((! [X6] : (! [X7] : (! [X8] : ((m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)))) & v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6) & v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)) & v1_funct_1(k10_tmap_1(X2,X6,X1,X0,X7,X8))) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6)))) | ~v5_pre_topc(X8,X0,X6) | ~v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6)) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6)))) | ~v5_pre_topc(X7,X1,X6) | ~v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6)) | ~v1_funct_1(X7)) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) & r1_tsep_1(X1,X0)) | ~sP0(X0,X1,X2)))),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 1.54/0.60  fof(f31,plain,(
% 1.54/0.60    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),X3) | ~v1_funct_2(k10_tmap_1(X2,X3,X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X2,X3,X1,X0,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X5,X0,X3) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X5,X0,sK3(X0,X1,X2)) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X4,X1,sK3(X0,X1,X2)) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X4)) & l1_pre_topc(sK3(X0,X1,X2)) & v2_pre_topc(sK3(X0,X1,X2)) & ~v2_struct_0(sK3(X0,X1,X2))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f32,plain,(
% 1.54/0.60    ! [X2,X1,X0] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X5,X0,sK3(X0,X1,X2)) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X4,X1,sK3(X0,X1,X2)) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X5,X0,sK3(X0,X1,X2)) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X5)) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2)) & v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(sK4(X0,X1,X2))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f33,plain,(
% 1.54/0.60    ! [X2,X1,X0] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(X5,X0,sK3(X0,X1,X2)) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | ~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)))) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) & v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2)) & v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) & v1_funct_1(sK5(X0,X1,X2))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f30,plain,(
% 1.54/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X2,X3,X1,X0,X4,X5),k1_tsep_1(X2,X1,X0),X3) | ~v1_funct_2(k10_tmap_1(X2,X3,X1,X0,X4,X5),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X2,X3,X1,X0,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X5,X0,X3) & v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X0)) & ((! [X6] : (! [X7] : (! [X8] : ((m1_subset_1(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)))) & v5_pre_topc(k10_tmap_1(X2,X6,X1,X0,X7,X8),k1_tsep_1(X2,X1,X0),X6) & v1_funct_2(k10_tmap_1(X2,X6,X1,X0,X7,X8),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X6)) & v1_funct_1(k10_tmap_1(X2,X6,X1,X0,X7,X8))) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X6)))) | ~v5_pre_topc(X8,X0,X6) | ~v1_funct_2(X8,u1_struct_0(X0),u1_struct_0(X6)) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X6)))) | ~v5_pre_topc(X7,X1,X6) | ~v1_funct_2(X7,u1_struct_0(X1),u1_struct_0(X6)) | ~v1_funct_1(X7)) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) & r1_tsep_1(X1,X0)) | ~sP0(X0,X1,X2)))),
% 1.54/0.60    inference(rectify,[],[f29])).
% 1.54/0.60  fof(f29,plain,(
% 1.54/0.60    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP0(X2,X1,X0)))),
% 1.54/0.60    inference(flattening,[],[f28])).
% 1.54/0.60  fof(f28,plain,(
% 1.54/0.60    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2))) & ((! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP0(X2,X1,X0)))),
% 1.54/0.60    inference(nnf_transformation,[],[f23])).
% 1.54/0.60  fof(f23,plain,(
% 1.54/0.60    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)))),
% 1.54/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.54/0.60  fof(f1073,plain,(
% 1.54/0.60    spl11_77 | spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_10 | spl11_21 | ~spl11_24 | ~spl11_42 | ~spl11_43 | ~spl11_45 | ~spl11_46 | ~spl11_47 | ~spl11_48 | ~spl11_52 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_65 | ~spl11_66),
% 1.54/0.60    inference(avatar_split_clause,[],[f921,f913,f908,f806,f801,f791,f786,f761,f756,f751,f746,f724,f719,f405,f379,f190,f172,f167,f162,f157,f152,f147,f142,f1070])).
% 1.54/0.60  fof(f142,plain,(
% 1.54/0.60    spl11_1 <=> v2_struct_0(sK6)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.54/0.60  fof(f147,plain,(
% 1.54/0.60    spl11_2 <=> v2_pre_topc(sK6)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.54/0.60  fof(f152,plain,(
% 1.54/0.60    spl11_3 <=> l1_pre_topc(sK6)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.54/0.60  fof(f157,plain,(
% 1.54/0.60    spl11_4 <=> v2_struct_0(sK7)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.54/0.60  fof(f162,plain,(
% 1.54/0.60    spl11_5 <=> v2_struct_0(sK8)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.54/0.60  fof(f167,plain,(
% 1.54/0.60    spl11_6 <=> m1_pre_topc(sK7,sK6)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.54/0.60  fof(f172,plain,(
% 1.54/0.60    spl11_7 <=> m1_pre_topc(sK8,sK6)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.54/0.60  fof(f190,plain,(
% 1.54/0.60    spl11_10 <=> r1_tsep_1(sK7,sK8)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 1.54/0.60  fof(f724,plain,(
% 1.54/0.60    spl11_43 <=> v1_funct_1(sK10(sK8,sK7,sK6))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).
% 1.54/0.60  fof(f746,plain,(
% 1.54/0.60    spl11_45 <=> v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).
% 1.54/0.60  fof(f761,plain,(
% 1.54/0.60    spl11_48 <=> m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6)))))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).
% 1.54/0.60  fof(f908,plain,(
% 1.54/0.60    spl11_65 <=> r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_65])])).
% 1.54/0.60  fof(f913,plain,(
% 1.54/0.60    spl11_66 <=> r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).
% 1.54/0.60  fof(f921,plain,(
% 1.54/0.60    sK10(sK8,sK7,sK6) = k10_tmap_1(sK6,sK9(sK8,sK7,sK6),sK7,sK8,k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_10 | spl11_21 | ~spl11_24 | ~spl11_42 | ~spl11_43 | ~spl11_45 | ~spl11_46 | ~spl11_47 | ~spl11_48 | ~spl11_52 | ~spl11_53 | ~spl11_55 | ~spl11_56 | ~spl11_65 | ~spl11_66)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f144,f149,f154,f174,f169,f381,f407,f721,f726,f748,f753,f758,f763,f788,f793,f803,f910,f808,f915,f672])).
% 1.54/0.60  fof(f672,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_pre_topc(sK8,X1) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK7,X2),X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0)) | ~v1_funct_1(X2) | k10_tmap_1(X1,X0,sK7,sK8,X4,X3) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~r2_funct_2(u1_struct_0(sK8),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK8,X2),X3) | ~m1_pre_topc(sK7,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (spl11_4 | spl11_5 | ~spl11_10)),
% 1.54/0.60    inference(subsumption_resolution,[],[f671,f159])).
% 1.54/0.60  fof(f159,plain,(
% 1.54/0.60    ~v2_struct_0(sK7) | spl11_4),
% 1.54/0.60    inference(avatar_component_clause,[],[f157])).
% 1.54/0.60  fof(f671,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X3,X1] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK8,X2),X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK7,X2),X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0)) | ~v1_funct_1(X2) | k10_tmap_1(X1,X0,sK7,sK8,X4,X3) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(sK8,X1) | ~m1_pre_topc(sK7,X1) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (spl11_5 | ~spl11_10)),
% 1.54/0.60    inference(subsumption_resolution,[],[f668,f164])).
% 1.54/0.60  fof(f164,plain,(
% 1.54/0.60    ~v2_struct_0(sK8) | spl11_5),
% 1.54/0.60    inference(avatar_component_clause,[],[f162])).
% 1.54/0.60  fof(f668,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X3,X1] : (~r2_funct_2(u1_struct_0(sK8),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK8,X2),X3) | ~r2_funct_2(u1_struct_0(sK7),u1_struct_0(X0),k3_tmap_1(X1,X0,k1_tsep_1(X1,sK7,sK8),sK7,X2),X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X1,sK7,sK8)),u1_struct_0(X0)) | ~v1_funct_1(X2) | k10_tmap_1(X1,X0,sK7,sK8,X4,X3) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X0)))) | ~v1_funct_2(X3,u1_struct_0(sK8),u1_struct_0(X0)) | ~v1_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(sK8,X1) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,X1) | v2_struct_0(sK7) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl11_10),
% 1.54/0.60    inference(resolution,[],[f192,f87])).
% 1.54/0.60  fof(f87,plain,(
% 1.54/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~r1_tsep_1(X2,X3) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6) | k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f42])).
% 1.54/0.60  fof(f42,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & ~r1_tsep_1(X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(flattening,[],[f41])).
% 1.54/0.60  fof(f41,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) & ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)) | k10_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & ~r1_tsep_1(X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(nnf_transformation,[],[f14])).
% 1.54/0.60  fof(f14,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6)) | (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & ~r1_tsep_1(X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(flattening,[],[f13])).
% 1.54/0.60  fof(f13,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4))) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X6))) | (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & ~r1_tsep_1(X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f2])).
% 1.54/0.60  fof(f2,axiom,(
% 1.54/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | r1_tsep_1(X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X6)) => (k10_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X6),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X6),X4)))))))))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_tmap_1)).
% 1.54/0.60  fof(f192,plain,(
% 1.54/0.60    r1_tsep_1(sK7,sK8) | ~spl11_10),
% 1.54/0.60    inference(avatar_component_clause,[],[f190])).
% 1.54/0.60  fof(f915,plain,(
% 1.54/0.60    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | ~spl11_66),
% 1.54/0.60    inference(avatar_component_clause,[],[f913])).
% 1.54/0.60  fof(f910,plain,(
% 1.54/0.60    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | ~spl11_65),
% 1.54/0.60    inference(avatar_component_clause,[],[f908])).
% 1.54/0.60  fof(f763,plain,(
% 1.54/0.60    m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | ~spl11_48),
% 1.54/0.60    inference(avatar_component_clause,[],[f761])).
% 1.54/0.60  fof(f748,plain,(
% 1.54/0.60    v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | ~spl11_45),
% 1.54/0.60    inference(avatar_component_clause,[],[f746])).
% 1.54/0.60  fof(f726,plain,(
% 1.54/0.60    v1_funct_1(sK10(sK8,sK7,sK6)) | ~spl11_43),
% 1.54/0.60    inference(avatar_component_clause,[],[f724])).
% 1.54/0.60  fof(f169,plain,(
% 1.54/0.60    m1_pre_topc(sK7,sK6) | ~spl11_6),
% 1.54/0.60    inference(avatar_component_clause,[],[f167])).
% 1.54/0.60  fof(f174,plain,(
% 1.54/0.60    m1_pre_topc(sK8,sK6) | ~spl11_7),
% 1.54/0.60    inference(avatar_component_clause,[],[f172])).
% 1.54/0.60  fof(f154,plain,(
% 1.54/0.60    l1_pre_topc(sK6) | ~spl11_3),
% 1.54/0.60    inference(avatar_component_clause,[],[f152])).
% 1.54/0.60  fof(f149,plain,(
% 1.54/0.60    v2_pre_topc(sK6) | ~spl11_2),
% 1.54/0.60    inference(avatar_component_clause,[],[f147])).
% 1.54/0.60  fof(f144,plain,(
% 1.54/0.60    ~v2_struct_0(sK6) | spl11_1),
% 1.54/0.60    inference(avatar_component_clause,[],[f142])).
% 1.54/0.60  fof(f916,plain,(
% 1.54/0.60    spl11_66 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f705,f327,f190,f913])).
% 1.54/0.60  fof(f327,plain,(
% 1.54/0.60    spl11_16 <=> sP1(sK8,sK7,sK6)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 1.54/0.60  fof(f705,plain,(
% 1.54/0.60    r2_funct_2(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f236])).
% 1.54/0.60  fof(f236,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) | ~r1_tsep_1(X1,X0) | sP1(X0,X1,X2)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f235,f106])).
% 1.54/0.60  fof(f106,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f49,plain,(
% 1.54/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((~m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(sK10(X0,X1,X2))) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) & v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(sK10(X0,X1,X2))) & l1_pre_topc(sK9(X0,X1,X2)) & v2_pre_topc(sK9(X0,X1,X2)) & ~v2_struct_0(sK9(X0,X1,X2))) | ~r1_tsep_1(X1,X0)) & ((! [X5] : (! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)))) & v5_pre_topc(X6,k1_tsep_1(X2,X1,X0),X5) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)) & v1_funct_1(X6)) | ~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5)))) | ~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),X0,X5) | ~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),u1_struct_0(X0),u1_struct_0(X5)) | ~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6)) | ~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),X1,X5) | ~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)) | ~v1_funct_1(X6)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) & r1_tsep_1(X1,X0)) | ~sP1(X0,X1,X2)))),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f46,f48,f47])).
% 1.54/0.60  fof(f47,plain,(
% 1.54/0.60    ! [X2,X1,X0] : (? [X3] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),X0,X3) & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4)) & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),X0,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4)) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),X1,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(X4)) & l1_pre_topc(sK9(X0,X1,X2)) & v2_pre_topc(sK9(X0,X1,X2)) & ~v2_struct_0(sK9(X0,X1,X2))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f48,plain,(
% 1.54/0.60    ! [X2,X1,X0] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),X0,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,X4)) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),X1,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(X4)) => ((~m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(sK10(X0,X1,X2))) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) & m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) & v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2)) & v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) & v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) & v1_funct_1(sK10(X0,X1,X2))))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f46,plain,(
% 1.54/0.60    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X2,X1,X0),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),X0,X3) & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4),u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X0,X4)) & m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X1,X0),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X0)) & ((! [X5] : (! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)))) & v5_pre_topc(X6,k1_tsep_1(X2,X1,X0),X5) & v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)) & v1_funct_1(X6)) | ~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X5)))) | ~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),X0,X5) | ~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6),u1_struct_0(X0),u1_struct_0(X5)) | ~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X0,X6)) | ~m1_subset_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X5)))) | ~v5_pre_topc(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),X1,X5) | ~v1_funct_2(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6),u1_struct_0(X1),u1_struct_0(X5)) | ~v1_funct_1(k3_tmap_1(X2,X5,k1_tsep_1(X2,X1,X0),X1,X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)))) | ~v1_funct_2(X6,u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(X5)) | ~v1_funct_1(X6)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5)) & r1_tsep_1(X1,X0)) | ~sP1(X0,X1,X2)))),
% 1.54/0.60    inference(rectify,[],[f45])).
% 1.54/0.60  fof(f45,plain,(
% 1.54/0.60    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | ? [X3] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2)) & ((! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP1(X2,X1,X0)))),
% 1.54/0.60    inference(flattening,[],[f44])).
% 1.54/0.60  fof(f44,plain,(
% 1.54/0.60    ! [X2,X1,X0] : ((sP1(X2,X1,X0) | (? [X3] : (? [X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) & l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) | ~r1_tsep_1(X1,X2))) & ((! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)) | ~sP1(X2,X1,X0)))),
% 1.54/0.60    inference(nnf_transformation,[],[f25])).
% 1.54/0.60  fof(f25,plain,(
% 1.54/0.60    ! [X2,X1,X0] : (sP1(X2,X1,X0) <=> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2)))),
% 1.54/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.54/0.60  fof(f235,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) | ~v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f234,f107])).
% 1.54/0.60  fof(f107,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f234,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0) | r2_funct_2(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2))) | ~v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)))) )),
% 1.54/0.60    inference(resolution,[],[f109,f125])).
% 1.54/0.60  fof(f125,plain,(
% 1.54/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.54/0.60    inference(duplicate_literal_removal,[],[f124])).
% 1.54/0.60  fof(f124,plain,(
% 1.54/0.60    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.54/0.60    inference(equality_resolution,[],[f116])).
% 1.54/0.60  fof(f116,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f52])).
% 1.54/0.60  fof(f52,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.60    inference(nnf_transformation,[],[f20])).
% 1.54/0.60  fof(f20,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.60    inference(flattening,[],[f19])).
% 1.54/0.60  fof(f19,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.54/0.60    inference(ennf_transformation,[],[f1])).
% 1.54/0.60  fof(f1,axiom,(
% 1.54/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.54/0.60  fof(f109,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK9(X0,X1,X2))))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f329,plain,(
% 1.54/0.60    ~sP1(sK8,sK7,sK6) | spl11_16),
% 1.54/0.60    inference(avatar_component_clause,[],[f327])).
% 1.54/0.60  fof(f911,plain,(
% 1.54/0.60    spl11_65 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f704,f327,f190,f908])).
% 1.54/0.60  fof(f704,plain,(
% 1.54/0.60    r2_funct_2(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f228])).
% 1.54/0.60  fof(f228,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (r2_funct_2(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) | ~r1_tsep_1(X1,X0) | sP1(X0,X1,X2)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f227,f102])).
% 1.54/0.60  fof(f102,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f227,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0) | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) | ~v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f226,f103])).
% 1.54/0.60  fof(f103,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f226,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0) | r2_funct_2(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2))) | ~v1_funct_2(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)))) )),
% 1.54/0.60    inference(resolution,[],[f105,f125])).
% 1.54/0.60  fof(f105,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK9(X0,X1,X2))))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f809,plain,(
% 1.54/0.60    spl11_56 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f701,f327,f190,f806])).
% 1.54/0.60  fof(f701,plain,(
% 1.54/0.60    m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f109])).
% 1.54/0.60  fof(f804,plain,(
% 1.54/0.60    spl11_55 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f697,f327,f190,f801])).
% 1.54/0.60  fof(f697,plain,(
% 1.54/0.60    m1_subset_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f105])).
% 1.54/0.60  fof(f794,plain,(
% 1.54/0.60    spl11_53 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f699,f327,f190,f791])).
% 1.54/0.60  fof(f699,plain,(
% 1.54/0.60    v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),u1_struct_0(sK8),u1_struct_0(sK9(sK8,sK7,sK6))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f107])).
% 1.54/0.60  fof(f789,plain,(
% 1.54/0.60    spl11_52 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f695,f327,f190,f786])).
% 1.54/0.60  fof(f695,plain,(
% 1.54/0.60    v1_funct_2(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),u1_struct_0(sK7),u1_struct_0(sK9(sK8,sK7,sK6))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f103])).
% 1.54/0.60  fof(f784,plain,(
% 1.54/0.60    spl11_51 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f700,f327,f190,f781])).
% 1.54/0.60  fof(f700,plain,(
% 1.54/0.60    v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6)),sK8,sK9(sK8,sK7,sK6)) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f108])).
% 1.54/0.60  fof(f108,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X0,sK10(X0,X1,X2)),X0,sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f779,plain,(
% 1.54/0.60    spl11_50 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f696,f327,f190,f776])).
% 1.54/0.60  fof(f696,plain,(
% 1.54/0.60    v5_pre_topc(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6)),sK7,sK9(sK8,sK7,sK6)) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f104])).
% 1.54/0.60  fof(f104,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v5_pre_topc(k3_tmap_1(X2,sK9(X0,X1,X2),k1_tsep_1(X2,X1,X0),X1,sK10(X0,X1,X2)),X1,sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f764,plain,(
% 1.54/0.60    spl11_48 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f693,f327,f190,f761])).
% 1.54/0.60  fof(f693,plain,(
% 1.54/0.60    m1_subset_1(sK10(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f101])).
% 1.54/0.60  fof(f101,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f759,plain,(
% 1.54/0.60    spl11_47 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f698,f327,f190,f756])).
% 1.54/0.60  fof(f698,plain,(
% 1.54/0.60    v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK8,sK10(sK8,sK7,sK6))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f106])).
% 1.54/0.60  fof(f754,plain,(
% 1.54/0.60    spl11_46 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f694,f327,f190,f751])).
% 1.54/0.60  fof(f694,plain,(
% 1.54/0.60    v1_funct_1(k3_tmap_1(sK6,sK9(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK7,sK10(sK8,sK7,sK6))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f102])).
% 1.54/0.60  fof(f749,plain,(
% 1.54/0.60    spl11_45 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f692,f327,f190,f746])).
% 1.54/0.60  fof(f692,plain,(
% 1.54/0.60    v1_funct_2(sK10(sK8,sK7,sK6),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK9(sK8,sK7,sK6))) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f100])).
% 1.54/0.60  fof(f100,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f744,plain,(
% 1.54/0.60    ~spl11_44 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f702,f327,f190,f741])).
% 1.54/0.60  fof(f702,plain,(
% 1.54/0.60    ~v5_pre_topc(sK10(sK8,sK7,sK6),k1_tsep_1(sK6,sK7,sK8),sK9(sK8,sK7,sK6)) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f128])).
% 1.54/0.60  fof(f128,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f127,f99])).
% 1.54/0.60  fof(f99,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_1(sK10(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f127,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_1(sK10(X0,X1,X2)) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f126,f100])).
% 1.54/0.60  fof(f126,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(sK10(X0,X1,X2)) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(subsumption_resolution,[],[f110,f101])).
% 1.54/0.60  fof(f110,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))))) | ~v5_pre_topc(sK10(X0,X1,X2),k1_tsep_1(X2,X1,X0),sK9(X0,X1,X2)) | ~v1_funct_2(sK10(X0,X1,X2),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK9(X0,X1,X2))) | ~v1_funct_1(sK10(X0,X1,X2)) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f727,plain,(
% 1.54/0.60    spl11_43 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f691,f327,f190,f724])).
% 1.54/0.60  fof(f691,plain,(
% 1.54/0.60    v1_funct_1(sK10(sK8,sK7,sK6)) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f99])).
% 1.54/0.60  fof(f722,plain,(
% 1.54/0.60    spl11_42 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f690,f327,f190,f719])).
% 1.54/0.60  fof(f690,plain,(
% 1.54/0.60    l1_pre_topc(sK9(sK8,sK7,sK6)) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f98])).
% 1.54/0.60  fof(f98,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (l1_pre_topc(sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f663,plain,(
% 1.54/0.60    spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | spl11_16),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f662])).
% 1.54/0.60  fof(f662,plain,(
% 1.54/0.60    $false | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8 | spl11_16)),
% 1.54/0.60    inference(subsumption_resolution,[],[f329,f661])).
% 1.54/0.60  fof(f661,plain,(
% 1.54/0.60    sP1(sK8,sK7,sK6) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_8)),
% 1.54/0.60    inference(subsumption_resolution,[],[f660,f164])).
% 1.54/0.60  fof(f660,plain,(
% 1.54/0.60    v2_struct_0(sK8) | sP1(sK8,sK7,sK6) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | ~spl11_6 | ~spl11_7 | ~spl11_8)),
% 1.54/0.60    inference(subsumption_resolution,[],[f425,f174])).
% 1.54/0.60  fof(f425,plain,(
% 1.54/0.60    ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | sP1(sK8,sK7,sK6) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | ~spl11_6 | ~spl11_8)),
% 1.54/0.60    inference(resolution,[],[f179,f285])).
% 1.54/0.60  fof(f285,plain,(
% 1.54/0.60    ( ! [X1] : (~r3_tsep_1(sK6,sK7,X1) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | sP1(X1,sK7,sK6)) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | ~spl11_6)),
% 1.54/0.60    inference(resolution,[],[f203,f89])).
% 1.54/0.60  fof(f89,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2) | sP1(X2,X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f43])).
% 1.54/0.60  fof(f43,plain,(
% 1.54/0.60    ! [X0,X1,X2] : (((r3_tsep_1(X0,X1,X2) | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | ~r3_tsep_1(X0,X1,X2))) | ~sP2(X0,X1,X2))),
% 1.54/0.60    inference(nnf_transformation,[],[f26])).
% 1.54/0.60  fof(f26,plain,(
% 1.54/0.60    ! [X0,X1,X2] : ((r3_tsep_1(X0,X1,X2) <=> sP1(X2,X1,X0)) | ~sP2(X0,X1,X2))),
% 1.54/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.54/0.60  fof(f203,plain,(
% 1.54/0.60    ( ! [X0] : (sP2(sK6,sK7,X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK6)) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | ~spl11_6)),
% 1.54/0.60    inference(subsumption_resolution,[],[f202,f144])).
% 1.54/0.60  fof(f202,plain,(
% 1.54/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK6) | v2_struct_0(X0) | sP2(sK6,sK7,X0) | v2_struct_0(sK6)) ) | (~spl11_2 | ~spl11_3 | spl11_4 | ~spl11_6)),
% 1.54/0.60    inference(subsumption_resolution,[],[f201,f149])).
% 1.54/0.60  fof(f201,plain,(
% 1.54/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK6) | v2_struct_0(X0) | sP2(sK6,sK7,X0) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) ) | (~spl11_3 | spl11_4 | ~spl11_6)),
% 1.54/0.60    inference(subsumption_resolution,[],[f200,f154])).
% 1.54/0.60  fof(f200,plain,(
% 1.54/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK6) | v2_struct_0(X0) | sP2(sK6,sK7,X0) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) ) | (spl11_4 | ~spl11_6)),
% 1.54/0.60    inference(subsumption_resolution,[],[f198,f159])).
% 1.54/0.60  fof(f198,plain,(
% 1.54/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK6) | v2_struct_0(X0) | sP2(sK6,sK7,X0) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) ) | ~spl11_6),
% 1.54/0.60    inference(resolution,[],[f111,f169])).
% 1.54/0.60  fof(f111,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | sP2(X0,X1,X2) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f27])).
% 1.54/0.60  fof(f27,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : (sP2(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(definition_folding,[],[f16,f26,f25])).
% 1.54/0.60  fof(f16,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(flattening,[],[f15])).
% 1.54/0.60  fof(f15,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | (~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f4])).
% 1.54/0.60  fof(f4,axiom,(
% 1.54/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2))))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_tmap_1)).
% 1.54/0.60  fof(f179,plain,(
% 1.54/0.60    r3_tsep_1(sK6,sK7,sK8) | ~spl11_8),
% 1.54/0.60    inference(avatar_component_clause,[],[f177])).
% 1.54/0.60  fof(f177,plain,(
% 1.54/0.60    spl11_8 <=> r3_tsep_1(sK6,sK7,sK8)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.54/0.60  fof(f648,plain,(
% 1.54/0.60    spl11_10 | ~spl11_16),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f647])).
% 1.54/0.60  fof(f647,plain,(
% 1.54/0.60    $false | (spl11_10 | ~spl11_16)),
% 1.54/0.60    inference(subsumption_resolution,[],[f191,f446])).
% 1.54/0.60  fof(f446,plain,(
% 1.54/0.60    r1_tsep_1(sK7,sK8) | ~spl11_16),
% 1.54/0.60    inference(resolution,[],[f328,f91])).
% 1.54/0.60  fof(f91,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f328,plain,(
% 1.54/0.60    sP1(sK8,sK7,sK6) | ~spl11_16),
% 1.54/0.60    inference(avatar_component_clause,[],[f327])).
% 1.54/0.60  fof(f191,plain,(
% 1.54/0.60    ~r1_tsep_1(sK7,sK8) | spl11_10),
% 1.54/0.60    inference(avatar_component_clause,[],[f190])).
% 1.54/0.60  fof(f643,plain,(
% 1.54/0.60    spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_9 | ~spl11_10 | ~spl11_15 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_30 | ~spl11_31 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35 | ~spl11_40),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f642])).
% 1.54/0.60  fof(f642,plain,(
% 1.54/0.60    $false | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_9 | ~spl11_10 | ~spl11_15 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_30 | ~spl11_31 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35 | ~spl11_40)),
% 1.54/0.60    inference(subsumption_resolution,[],[f641,f192])).
% 1.54/0.60  fof(f641,plain,(
% 1.54/0.60    ~r1_tsep_1(sK7,sK8) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_9 | ~spl11_10 | ~spl11_15 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_30 | ~spl11_31 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35 | ~spl11_40)),
% 1.54/0.60    inference(subsumption_resolution,[],[f640,f182])).
% 1.54/0.60  fof(f182,plain,(
% 1.54/0.60    ~sP0(sK8,sK7,sK6) | spl11_9),
% 1.54/0.60    inference(avatar_component_clause,[],[f181])).
% 1.54/0.60  fof(f640,plain,(
% 1.54/0.60    sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_10 | ~spl11_15 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_30 | ~spl11_31 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35 | ~spl11_40)),
% 1.54/0.60    inference(subsumption_resolution,[],[f639,f526])).
% 1.54/0.60  fof(f526,plain,(
% 1.54/0.60    v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f144,f149,f154,f164,f169,f174,f159,f450,f455,f460,f465,f470,f485,f495,f490,f500,f118])).
% 1.54/0.60  fof(f118,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f22])).
% 1.54/0.60  fof(f22,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(flattening,[],[f21])).
% 1.54/0.60  fof(f21,plain,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f3])).
% 1.54/0.60  fof(f3,axiom,(
% 1.54/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 1.54/0.60  fof(f500,plain,(
% 1.54/0.60    m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~spl11_35),
% 1.54/0.60    inference(avatar_component_clause,[],[f498])).
% 1.54/0.60  fof(f498,plain,(
% 1.54/0.60    spl11_35 <=> m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_35])])).
% 1.54/0.60  fof(f490,plain,(
% 1.54/0.60    v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | ~spl11_33),
% 1.54/0.60    inference(avatar_component_clause,[],[f488])).
% 1.54/0.60  fof(f488,plain,(
% 1.54/0.60    spl11_33 <=> v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6)))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).
% 1.54/0.60  fof(f495,plain,(
% 1.54/0.60    m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~spl11_34),
% 1.54/0.60    inference(avatar_component_clause,[],[f493])).
% 1.54/0.60  fof(f493,plain,(
% 1.54/0.60    spl11_34 <=> m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).
% 1.54/0.60  fof(f485,plain,(
% 1.54/0.60    v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | ~spl11_32),
% 1.54/0.60    inference(avatar_component_clause,[],[f483])).
% 1.54/0.60  fof(f483,plain,(
% 1.54/0.60    spl11_32 <=> v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6)))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).
% 1.54/0.60  fof(f470,plain,(
% 1.54/0.60    v1_funct_1(sK5(sK8,sK7,sK6)) | ~spl11_29),
% 1.54/0.60    inference(avatar_component_clause,[],[f468])).
% 1.54/0.60  fof(f468,plain,(
% 1.54/0.60    spl11_29 <=> v1_funct_1(sK5(sK8,sK7,sK6))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).
% 1.54/0.60  fof(f465,plain,(
% 1.54/0.60    v1_funct_1(sK4(sK8,sK7,sK6)) | ~spl11_28),
% 1.54/0.60    inference(avatar_component_clause,[],[f463])).
% 1.54/0.60  fof(f463,plain,(
% 1.54/0.60    spl11_28 <=> v1_funct_1(sK4(sK8,sK7,sK6))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).
% 1.54/0.60  fof(f460,plain,(
% 1.54/0.60    l1_pre_topc(sK3(sK8,sK7,sK6)) | ~spl11_27),
% 1.54/0.60    inference(avatar_component_clause,[],[f458])).
% 1.54/0.60  fof(f458,plain,(
% 1.54/0.60    spl11_27 <=> l1_pre_topc(sK3(sK8,sK7,sK6))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).
% 1.54/0.60  fof(f455,plain,(
% 1.54/0.60    v2_pre_topc(sK3(sK8,sK7,sK6)) | ~spl11_26),
% 1.54/0.60    inference(avatar_component_clause,[],[f453])).
% 1.54/0.60  fof(f453,plain,(
% 1.54/0.60    spl11_26 <=> v2_pre_topc(sK3(sK8,sK7,sK6))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).
% 1.54/0.60  fof(f450,plain,(
% 1.54/0.60    ~v2_struct_0(sK3(sK8,sK7,sK6)) | spl11_25),
% 1.54/0.60    inference(avatar_component_clause,[],[f448])).
% 1.54/0.60  fof(f448,plain,(
% 1.54/0.60    spl11_25 <=> v2_struct_0(sK3(sK8,sK7,sK6))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).
% 1.54/0.60  fof(f639,plain,(
% 1.54/0.60    ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_10 | ~spl11_15 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_30 | ~spl11_31 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35 | ~spl11_40)),
% 1.54/0.60    inference(subsumption_resolution,[],[f638,f518])).
% 1.54/0.60  fof(f518,plain,(
% 1.54/0.60    v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_10 | ~spl11_15 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_30 | ~spl11_31 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f144,f149,f154,f164,f159,f174,f192,f169,f315,f450,f455,f460,f465,f470,f475,f485,f495,f480,f490,f500,f81])).
% 1.54/0.60  fof(f81,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f12])).
% 1.54/0.60  % (16332)Refutation not found, incomplete strategy% (16332)------------------------------
% 1.54/0.60  % (16332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.60  % (16332)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.60  
% 1.54/0.60  % (16332)Memory used [KB]: 6140
% 1.54/0.60  % (16332)Time elapsed: 0.185 s
% 1.54/0.60  % (16332)------------------------------
% 1.54/0.60  % (16332)------------------------------
% 1.54/0.60  fof(f12,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(flattening,[],[f11])).
% 1.54/0.60  fof(f11,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f5])).
% 1.54/0.60  fof(f5,axiom,(
% 1.54/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r4_tsep_1(X0,X2,X3) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_tmap_1)).
% 1.54/0.60  fof(f480,plain,(
% 1.54/0.60    v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | ~spl11_31),
% 1.54/0.60    inference(avatar_component_clause,[],[f478])).
% 1.54/0.60  fof(f478,plain,(
% 1.54/0.60    spl11_31 <=> v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 1.54/0.60  fof(f475,plain,(
% 1.54/0.60    v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | ~spl11_30),
% 1.54/0.60    inference(avatar_component_clause,[],[f473])).
% 1.54/0.60  fof(f473,plain,(
% 1.54/0.60    spl11_30 <=> v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
% 1.54/0.60  fof(f315,plain,(
% 1.54/0.60    r4_tsep_1(sK6,sK7,sK8) | ~spl11_15),
% 1.54/0.60    inference(avatar_component_clause,[],[f314])).
% 1.54/0.60  fof(f314,plain,(
% 1.54/0.60    spl11_15 <=> r4_tsep_1(sK6,sK7,sK8)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 1.54/0.60  fof(f638,plain,(
% 1.54/0.60    ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35 | ~spl11_40)),
% 1.54/0.60    inference(subsumption_resolution,[],[f637,f530])).
% 1.54/0.60  fof(f530,plain,(
% 1.54/0.60    m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f144,f149,f154,f164,f169,f174,f159,f450,f455,f460,f465,f470,f485,f495,f490,f500,f119])).
% 1.54/0.60  fof(f119,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f22])).
% 1.54/0.60  fof(f637,plain,(
% 1.54/0.60    ~m1_subset_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))))) | ~v5_pre_topc(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),k1_tsep_1(sK6,sK7,sK8),sK3(sK8,sK7,sK6)) | ~v1_funct_2(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)),u1_struct_0(k1_tsep_1(sK6,sK7,sK8)),u1_struct_0(sK3(sK8,sK7,sK6))) | sP0(sK8,sK7,sK6) | ~r1_tsep_1(sK7,sK8) | ~spl11_40),
% 1.54/0.60    inference(resolution,[],[f630,f69])).
% 1.54/0.60  fof(f69,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2))) | ~m1_subset_1(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))))) | ~v5_pre_topc(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),k1_tsep_1(X2,X1,X0),sK3(X0,X1,X2)) | ~v1_funct_2(k10_tmap_1(X2,sK3(X0,X1,X2),X1,X0,sK4(X0,X1,X2),sK5(X0,X1,X2)),u1_struct_0(k1_tsep_1(X2,X1,X0)),u1_struct_0(sK3(X0,X1,X2))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f630,plain,(
% 1.54/0.60    v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6))) | ~spl11_40),
% 1.54/0.60    inference(avatar_component_clause,[],[f628])).
% 1.54/0.60  fof(f628,plain,(
% 1.54/0.60    spl11_40 <=> v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6)))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).
% 1.54/0.60  fof(f631,plain,(
% 1.54/0.60    spl11_40 | spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35),
% 1.54/0.60    inference(avatar_split_clause,[],[f534,f498,f493,f488,f483,f468,f463,f458,f453,f448,f172,f167,f162,f157,f152,f147,f142,f628])).
% 1.54/0.60  fof(f534,plain,(
% 1.54/0.60    v1_funct_1(k10_tmap_1(sK6,sK3(sK8,sK7,sK6),sK7,sK8,sK4(sK8,sK7,sK6),sK5(sK8,sK7,sK6))) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_25 | ~spl11_26 | ~spl11_27 | ~spl11_28 | ~spl11_29 | ~spl11_32 | ~spl11_33 | ~spl11_34 | ~spl11_35)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f164,f174,f450,f455,f460,f470,f465,f485,f495,f490,f500,f243])).
% 1.54/0.60  fof(f243,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X1,sK6) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | ~spl11_6)),
% 1.54/0.60    inference(subsumption_resolution,[],[f242,f144])).
% 1.54/0.60  fof(f242,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v2_struct_0(sK6)) ) | (~spl11_2 | ~spl11_3 | spl11_4 | ~spl11_6)),
% 1.54/0.60    inference(subsumption_resolution,[],[f241,f149])).
% 1.54/0.60  fof(f241,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) ) | (~spl11_3 | spl11_4 | ~spl11_6)),
% 1.54/0.60    inference(subsumption_resolution,[],[f240,f154])).
% 1.54/0.60  fof(f240,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) ) | (spl11_4 | ~spl11_6)),
% 1.54/0.60    inference(subsumption_resolution,[],[f238,f159])).
% 1.54/0.60  fof(f238,plain,(
% 1.54/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(sK7),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~m1_pre_topc(X1,sK6) | v2_struct_0(X1) | v1_funct_1(k10_tmap_1(sK6,X2,sK7,X1,X3,X0)) | v2_struct_0(sK7) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6)) ) | ~spl11_6),
% 1.54/0.60    inference(resolution,[],[f117,f169])).
% 1.54/0.60  fof(f117,plain,(
% 1.54/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_pre_topc(X2,X0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f22])).
% 1.54/0.60  fof(f501,plain,(
% 1.54/0.60    spl11_35 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f437,f190,f181,f498])).
% 1.54/0.60  fof(f437,plain,(
% 1.54/0.60    m1_subset_1(sK5(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))))) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f68])).
% 1.54/0.60  fof(f68,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f496,plain,(
% 1.54/0.60    spl11_34 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f433,f190,f181,f493])).
% 1.54/0.60  fof(f433,plain,(
% 1.54/0.60    m1_subset_1(sK4(sK8,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))))) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f64])).
% 1.54/0.60  fof(f64,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f491,plain,(
% 1.54/0.60    spl11_33 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f435,f190,f181,f488])).
% 1.54/0.60  fof(f435,plain,(
% 1.54/0.60    v1_funct_2(sK5(sK8,sK7,sK6),u1_struct_0(sK8),u1_struct_0(sK3(sK8,sK7,sK6))) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f66])).
% 1.54/0.60  fof(f66,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_2(sK5(X0,X1,X2),u1_struct_0(X0),u1_struct_0(sK3(X0,X1,X2))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f486,plain,(
% 1.54/0.60    spl11_32 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f431,f190,f181,f483])).
% 1.54/0.60  fof(f431,plain,(
% 1.54/0.60    v1_funct_2(sK4(sK8,sK7,sK6),u1_struct_0(sK7),u1_struct_0(sK3(sK8,sK7,sK6))) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f62])).
% 1.54/0.60  fof(f62,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_2(sK4(X0,X1,X2),u1_struct_0(X1),u1_struct_0(sK3(X0,X1,X2))) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f481,plain,(
% 1.54/0.60    spl11_31 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f436,f190,f181,f478])).
% 1.54/0.60  fof(f436,plain,(
% 1.54/0.60    v5_pre_topc(sK5(sK8,sK7,sK6),sK8,sK3(sK8,sK7,sK6)) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f67])).
% 1.54/0.60  fof(f67,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v5_pre_topc(sK5(X0,X1,X2),X0,sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f476,plain,(
% 1.54/0.60    spl11_30 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f432,f190,f181,f473])).
% 1.54/0.60  fof(f432,plain,(
% 1.54/0.60    v5_pre_topc(sK4(sK8,sK7,sK6),sK7,sK3(sK8,sK7,sK6)) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f63])).
% 1.54/0.60  fof(f63,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v5_pre_topc(sK4(X0,X1,X2),X1,sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f471,plain,(
% 1.54/0.60    spl11_29 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f434,f190,f181,f468])).
% 1.54/0.60  fof(f434,plain,(
% 1.54/0.60    v1_funct_1(sK5(sK8,sK7,sK6)) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f65])).
% 1.54/0.60  fof(f65,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_1(sK5(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f466,plain,(
% 1.54/0.60    spl11_28 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f430,f190,f181,f463])).
% 1.54/0.60  fof(f430,plain,(
% 1.54/0.60    v1_funct_1(sK4(sK8,sK7,sK6)) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f61])).
% 1.54/0.60  fof(f61,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v1_funct_1(sK4(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f461,plain,(
% 1.54/0.60    spl11_27 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f429,f190,f181,f458])).
% 1.54/0.60  fof(f429,plain,(
% 1.54/0.60    l1_pre_topc(sK3(sK8,sK7,sK6)) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f60])).
% 1.54/0.60  fof(f60,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (l1_pre_topc(sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f456,plain,(
% 1.54/0.60    spl11_26 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f428,f190,f181,f453])).
% 1.54/0.60  fof(f428,plain,(
% 1.54/0.60    v2_pre_topc(sK3(sK8,sK7,sK6)) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f59])).
% 1.54/0.60  fof(f59,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v2_pre_topc(sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f451,plain,(
% 1.54/0.60    ~spl11_25 | spl11_9 | ~spl11_10),
% 1.54/0.60    inference(avatar_split_clause,[],[f427,f190,f181,f448])).
% 1.54/0.60  fof(f427,plain,(
% 1.54/0.60    ~v2_struct_0(sK3(sK8,sK7,sK6)) | (spl11_9 | ~spl11_10)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f182,f58])).
% 1.54/0.60  fof(f58,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~v2_struct_0(sK3(X0,X1,X2)) | sP0(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f418,plain,(
% 1.54/0.60    spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_12 | spl11_15 | ~spl11_16),
% 1.54/0.60    inference(avatar_contradiction_clause,[],[f417])).
% 1.54/0.60  fof(f417,plain,(
% 1.54/0.60    $false | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_12 | spl11_15 | ~spl11_16)),
% 1.54/0.60    inference(subsumption_resolution,[],[f328,f416])).
% 1.54/0.60  fof(f416,plain,(
% 1.54/0.60    ~sP1(sK8,sK7,sK6) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | ~spl11_12 | spl11_15)),
% 1.54/0.60    inference(subsumption_resolution,[],[f276,f415])).
% 1.54/0.60  fof(f415,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_15)),
% 1.54/0.60    inference(subsumption_resolution,[],[f414,f144])).
% 1.54/0.60  fof(f414,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | v2_struct_0(sK6) | (~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_15)),
% 1.54/0.60    inference(subsumption_resolution,[],[f413,f149])).
% 1.54/0.60  fof(f413,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | (~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_15)),
% 1.54/0.60    inference(subsumption_resolution,[],[f412,f154])).
% 1.54/0.60  fof(f412,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | (spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7 | spl11_15)),
% 1.54/0.60    inference(subsumption_resolution,[],[f411,f159])).
% 1.54/0.60  fof(f411,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | (spl11_5 | ~spl11_6 | ~spl11_7 | spl11_15)),
% 1.54/0.60    inference(subsumption_resolution,[],[f410,f169])).
% 1.54/0.60  fof(f410,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | (spl11_5 | ~spl11_7 | spl11_15)),
% 1.54/0.60    inference(subsumption_resolution,[],[f409,f164])).
% 1.54/0.60  fof(f409,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | (~spl11_7 | spl11_15)),
% 1.54/0.60    inference(subsumption_resolution,[],[f332,f174])).
% 1.54/0.60  fof(f332,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | spl11_15),
% 1.54/0.60    inference(resolution,[],[f316,f114])).
% 1.54/0.60  fof(f114,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~r3_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f51])).
% 1.54/0.60  fof(f51,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : ((((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2)) & (r3_tsep_1(X0,X1,X2) | ~r4_tsep_1(X0,X1,X2) | ~r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(flattening,[],[f50])).
% 1.54/0.60  fof(f50,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : ((((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) | ~r3_tsep_1(X0,X1,X2)) & (r3_tsep_1(X0,X1,X2) | (~r4_tsep_1(X0,X1,X2) | ~r1_tsep_1(X1,X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(nnf_transformation,[],[f18])).
% 1.54/0.60  fof(f18,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : (((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.60    inference(flattening,[],[f17])).
% 1.54/0.60  fof(f17,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (! [X2] : (((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f6])).
% 1.54/0.60  fof(f6,axiom,(
% 1.54/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ((r4_tsep_1(X0,X1,X2) & r1_tsep_1(X1,X2)) <=> r3_tsep_1(X0,X1,X2)))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tsep_1)).
% 1.54/0.60  fof(f316,plain,(
% 1.54/0.60    ~r4_tsep_1(sK6,sK7,sK8) | spl11_15),
% 1.54/0.60    inference(avatar_component_clause,[],[f314])).
% 1.54/0.60  fof(f276,plain,(
% 1.54/0.60    ~sP1(sK8,sK7,sK6) | r3_tsep_1(sK6,sK7,sK8) | ~spl11_12),
% 1.54/0.60    inference(resolution,[],[f232,f90])).
% 1.54/0.60  fof(f90,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f43])).
% 1.54/0.60  % (16343)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.54/0.60  fof(f232,plain,(
% 1.54/0.60    sP2(sK6,sK7,sK8) | ~spl11_12),
% 1.54/0.60    inference(avatar_component_clause,[],[f230])).
% 1.54/0.60  fof(f230,plain,(
% 1.54/0.60    spl11_12 <=> sP2(sK6,sK7,sK8)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 1.54/0.60  fof(f408,plain,(
% 1.54/0.60    spl11_24 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f335,f327,f190,f405])).
% 1.54/0.60  fof(f335,plain,(
% 1.54/0.60    v2_pre_topc(sK9(sK8,sK7,sK6)) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f97])).
% 1.54/0.60  fof(f97,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (v2_pre_topc(sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f382,plain,(
% 1.54/0.60    ~spl11_21 | ~spl11_10 | spl11_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f334,f327,f190,f379])).
% 1.54/0.60  fof(f334,plain,(
% 1.54/0.60    ~v2_struct_0(sK9(sK8,sK7,sK6)) | (~spl11_10 | spl11_16)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f192,f329,f96])).
% 1.54/0.60  fof(f96,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~v2_struct_0(sK9(X0,X1,X2)) | sP1(X0,X1,X2) | ~r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f49])).
% 1.54/0.60  fof(f330,plain,(
% 1.54/0.60    ~spl11_16 | spl11_8 | ~spl11_12),
% 1.54/0.60    inference(avatar_split_clause,[],[f275,f230,f177,f327])).
% 1.54/0.60  fof(f275,plain,(
% 1.54/0.60    ~sP1(sK8,sK7,sK6) | (spl11_8 | ~spl11_12)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f178,f232,f90])).
% 1.54/0.60  fof(f178,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | spl11_8),
% 1.54/0.60    inference(avatar_component_clause,[],[f177])).
% 1.54/0.60  fof(f233,plain,(
% 1.54/0.60    spl11_12 | spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7),
% 1.54/0.60    inference(avatar_split_clause,[],[f195,f172,f167,f162,f157,f152,f147,f142,f230])).
% 1.54/0.60  fof(f195,plain,(
% 1.54/0.60    sP2(sK6,sK7,sK8) | (spl11_1 | ~spl11_2 | ~spl11_3 | spl11_4 | spl11_5 | ~spl11_6 | ~spl11_7)),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f144,f149,f154,f159,f164,f174,f169,f111])).
% 1.54/0.60  fof(f193,plain,(
% 1.54/0.60    spl11_10 | ~spl11_9),
% 1.54/0.60    inference(avatar_split_clause,[],[f187,f181,f190])).
% 1.54/0.60  fof(f187,plain,(
% 1.54/0.60    r1_tsep_1(sK7,sK8) | ~spl11_9),
% 1.54/0.60    inference(unit_resulting_resolution,[],[f183,f53])).
% 1.54/0.60  fof(f53,plain,(
% 1.54/0.60    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_tsep_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f34])).
% 1.54/0.60  fof(f186,plain,(
% 1.54/0.60    ~spl11_8 | ~spl11_9),
% 1.54/0.60    inference(avatar_split_clause,[],[f185,f181,f177])).
% 1.54/0.60  fof(f185,plain,(
% 1.54/0.60    ~r3_tsep_1(sK6,sK7,sK8) | ~spl11_9),
% 1.54/0.60    inference(subsumption_resolution,[],[f78,f183])).
% 1.54/0.60  fof(f78,plain,(
% 1.54/0.60    ~sP0(sK8,sK7,sK6) | ~r3_tsep_1(sK6,sK7,sK8)),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  fof(f40,plain,(
% 1.54/0.60    (((~sP0(sK8,sK7,sK6) | ~r3_tsep_1(sK6,sK7,sK8)) & (sP0(sK8,sK7,sK6) | r3_tsep_1(sK6,sK7,sK8)) & m1_pre_topc(sK8,sK6) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK6) & ~v2_struct_0(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 1.54/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f36,f39,f38,f37])).
% 1.54/0.60  fof(f37,plain,(
% 1.54/0.60    ? [X0] : (? [X1] : (? [X2] : ((~sP0(X2,X1,X0) | ~r3_tsep_1(X0,X1,X2)) & (sP0(X2,X1,X0) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~sP0(X2,X1,sK6) | ~r3_tsep_1(sK6,X1,X2)) & (sP0(X2,X1,sK6) | r3_tsep_1(sK6,X1,X2)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK6) & ~v2_struct_0(X1)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f38,plain,(
% 1.54/0.60    ? [X1] : (? [X2] : ((~sP0(X2,X1,sK6) | ~r3_tsep_1(sK6,X1,X2)) & (sP0(X2,X1,sK6) | r3_tsep_1(sK6,X1,X2)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK6) & ~v2_struct_0(X1)) => (? [X2] : ((~sP0(X2,sK7,sK6) | ~r3_tsep_1(sK6,sK7,X2)) & (sP0(X2,sK7,sK6) | r3_tsep_1(sK6,sK7,X2)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(sK7,sK6) & ~v2_struct_0(sK7))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f39,plain,(
% 1.54/0.60    ? [X2] : ((~sP0(X2,sK7,sK6) | ~r3_tsep_1(sK6,sK7,X2)) & (sP0(X2,sK7,sK6) | r3_tsep_1(sK6,sK7,X2)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) => ((~sP0(sK8,sK7,sK6) | ~r3_tsep_1(sK6,sK7,sK8)) & (sP0(sK8,sK7,sK6) | r3_tsep_1(sK6,sK7,sK8)) & m1_pre_topc(sK8,sK6) & ~v2_struct_0(sK8))),
% 1.54/0.60    introduced(choice_axiom,[])).
% 1.54/0.60  fof(f36,plain,(
% 1.54/0.60    ? [X0] : (? [X1] : (? [X2] : ((~sP0(X2,X1,X0) | ~r3_tsep_1(X0,X1,X2)) & (sP0(X2,X1,X0) | r3_tsep_1(X0,X1,X2)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.54/0.60    inference(flattening,[],[f35])).
% 1.54/0.60  fof(f35,plain,(
% 1.54/0.60    ? [X0] : (? [X1] : (? [X2] : (((~sP0(X2,X1,X0) | ~r3_tsep_1(X0,X1,X2)) & (sP0(X2,X1,X0) | r3_tsep_1(X0,X1,X2))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.54/0.60    inference(nnf_transformation,[],[f24])).
% 1.54/0.60  fof(f24,plain,(
% 1.54/0.60    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> sP0(X2,X1,X0)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.54/0.60    inference(definition_folding,[],[f10,f23])).
% 1.54/0.60  fof(f10,plain,(
% 1.54/0.60    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.54/0.60    inference(flattening,[],[f9])).
% 1.54/0.60  fof(f9,plain,(
% 1.54/0.60    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(X5,X2,X3) | ~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(X4,X1,X3) | ~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f8])).
% 1.54/0.60  fof(f8,negated_conjecture,(
% 1.54/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)))))) & r1_tsep_1(X1,X2))))))),
% 1.54/0.60    inference(negated_conjecture,[],[f7])).
% 1.54/0.60  fof(f7,conjecture,(
% 1.54/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(X4,X1,X3) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(X5,X2,X3) & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(X5)) => (m1_subset_1(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(k10_tmap_1(X0,X3,X1,X2,X4,X5),k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(k10_tmap_1(X0,X3,X1,X2,X4,X5),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(k10_tmap_1(X0,X3,X1,X2,X4,X5)))))) & r1_tsep_1(X1,X2))))))),
% 1.54/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_tmap_1)).
% 1.54/0.60  fof(f184,plain,(
% 1.54/0.60    spl11_8 | spl11_9),
% 1.54/0.60    inference(avatar_split_clause,[],[f77,f181,f177])).
% 1.54/0.60  fof(f77,plain,(
% 1.54/0.60    sP0(sK8,sK7,sK6) | r3_tsep_1(sK6,sK7,sK8)),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  fof(f175,plain,(
% 1.54/0.60    spl11_7),
% 1.54/0.60    inference(avatar_split_clause,[],[f76,f172])).
% 1.54/0.60  fof(f76,plain,(
% 1.54/0.60    m1_pre_topc(sK8,sK6)),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  fof(f170,plain,(
% 1.54/0.60    spl11_6),
% 1.54/0.60    inference(avatar_split_clause,[],[f74,f167])).
% 1.54/0.60  fof(f74,plain,(
% 1.54/0.60    m1_pre_topc(sK7,sK6)),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  fof(f165,plain,(
% 1.54/0.60    ~spl11_5),
% 1.54/0.60    inference(avatar_split_clause,[],[f75,f162])).
% 1.54/0.60  fof(f75,plain,(
% 1.54/0.60    ~v2_struct_0(sK8)),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  fof(f160,plain,(
% 1.54/0.60    ~spl11_4),
% 1.54/0.60    inference(avatar_split_clause,[],[f73,f157])).
% 1.54/0.60  fof(f73,plain,(
% 1.54/0.60    ~v2_struct_0(sK7)),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  fof(f155,plain,(
% 1.54/0.60    spl11_3),
% 1.54/0.60    inference(avatar_split_clause,[],[f72,f152])).
% 1.54/0.60  fof(f72,plain,(
% 1.54/0.60    l1_pre_topc(sK6)),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  fof(f150,plain,(
% 1.54/0.60    spl11_2),
% 1.54/0.60    inference(avatar_split_clause,[],[f71,f147])).
% 1.54/0.60  fof(f71,plain,(
% 1.54/0.60    v2_pre_topc(sK6)),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  fof(f145,plain,(
% 1.54/0.60    ~spl11_1),
% 1.54/0.60    inference(avatar_split_clause,[],[f70,f142])).
% 1.54/0.60  fof(f70,plain,(
% 1.54/0.60    ~v2_struct_0(sK6)),
% 1.54/0.60    inference(cnf_transformation,[],[f40])).
% 1.54/0.60  % SZS output end Proof for theBenchmark
% 1.54/0.60  % (16346)------------------------------
% 1.54/0.60  % (16346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.60  % (16346)Termination reason: Refutation
% 1.54/0.60  
% 1.54/0.60  % (16346)Memory used [KB]: 13688
% 1.54/0.60  % (16346)Time elapsed: 0.173 s
% 1.54/0.60  % (16346)------------------------------
% 1.54/0.60  % (16346)------------------------------
% 1.54/0.60  % (16322)Success in time 0.233 s
%------------------------------------------------------------------------------
