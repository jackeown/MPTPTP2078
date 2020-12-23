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
% DateTime   : Thu Dec  3 13:19:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  299 (1404 expanded)
%              Number of leaves         :   62 ( 475 expanded)
%              Depth                    :    9
%              Number of atoms          : 1688 (21962 expanded)
%              Number of equality atoms :   51 ( 775 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f945,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f73,f77,f81,f85,f89,f93,f97,f101,f105,f109,f113,f117,f121,f125,f132,f136,f142,f165,f167,f170,f173,f176,f194,f222,f277,f306,f339,f344,f360,f636,f647,f652,f657,f662,f667,f672,f677,f682,f687,f690,f692,f728,f732,f761,f765,f771,f773,f775,f810,f812,f896,f914,f918,f920,f927,f929,f931,f944])).

fof(f944,plain,
    ( ~ spl7_71
    | ~ spl7_83
    | ~ spl7_92
    | spl7_103 ),
    inference(avatar_contradiction_clause,[],[f932])).

fof(f932,plain,
    ( $false
    | ~ spl7_71
    | ~ spl7_83
    | ~ spl7_92
    | spl7_103 ),
    inference(resolution,[],[f922,f886])).

fof(f886,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | spl7_103 ),
    inference(avatar_component_clause,[],[f885])).

fof(f885,plain,
    ( spl7_103
  <=> m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f922,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ spl7_71
    | ~ spl7_83
    | ~ spl7_92 ),
    inference(backward_demodulation,[],[f656,f921])).

fof(f921,plain,
    ( k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1)
    | ~ spl7_83
    | ~ spl7_92 ),
    inference(forward_demodulation,[],[f764,f727])).

fof(f727,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1)
    | ~ spl7_83 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl7_83
  <=> k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f764,plain,
    ( k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f763])).

fof(f763,plain,
    ( spl7_92
  <=> k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f656,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f655])).

fof(f655,plain,
    ( spl7_71
  <=> m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f931,plain,
    ( ~ spl7_73
    | ~ spl7_83
    | ~ spl7_92
    | spl7_101 ),
    inference(avatar_contradiction_clause,[],[f930])).

fof(f930,plain,
    ( $false
    | ~ spl7_73
    | ~ spl7_83
    | ~ spl7_92
    | spl7_101 ),
    inference(resolution,[],[f923,f880])).

fof(f880,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))
    | spl7_101 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl7_101
  <=> v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f923,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ spl7_73
    | ~ spl7_83
    | ~ spl7_92 ),
    inference(backward_demodulation,[],[f666,f921])).

fof(f666,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f665])).

fof(f665,plain,
    ( spl7_73
  <=> v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f929,plain,
    ( ~ spl7_75
    | ~ spl7_83
    | ~ spl7_92
    | spl7_102 ),
    inference(avatar_contradiction_clause,[],[f928])).

fof(f928,plain,
    ( $false
    | ~ spl7_75
    | ~ spl7_83
    | ~ spl7_92
    | spl7_102 ),
    inference(resolution,[],[f924,f883])).

fof(f883,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2))
    | spl7_102 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl7_102
  <=> v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f924,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2))
    | ~ spl7_75
    | ~ spl7_83
    | ~ spl7_92 ),
    inference(backward_demodulation,[],[f676,f921])).

fof(f676,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),sK1,sK5(sK0,sK1,sK2))
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f675])).

fof(f675,plain,
    ( spl7_75
  <=> v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),sK1,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f927,plain,
    ( ~ spl7_76
    | ~ spl7_83
    | ~ spl7_92
    | spl7_100 ),
    inference(avatar_contradiction_clause,[],[f926])).

fof(f926,plain,
    ( $false
    | ~ spl7_76
    | ~ spl7_83
    | ~ spl7_92
    | spl7_100 ),
    inference(resolution,[],[f925,f877])).

fof(f877,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1))
    | spl7_100 ),
    inference(avatar_component_clause,[],[f876])).

fof(f876,plain,
    ( spl7_100
  <=> v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f925,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1))
    | ~ spl7_76
    | ~ spl7_83
    | ~ spl7_92 ),
    inference(backward_demodulation,[],[f681,f921])).

fof(f681,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)))
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f680])).

fof(f680,plain,
    ( spl7_76
  <=> v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f920,plain,
    ( ~ spl7_72
    | ~ spl7_84
    | ~ spl7_91
    | spl7_105 ),
    inference(avatar_contradiction_clause,[],[f919])).

fof(f919,plain,
    ( $false
    | ~ spl7_72
    | ~ spl7_84
    | ~ spl7_91
    | spl7_105 ),
    inference(resolution,[],[f892,f860])).

fof(f860,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ spl7_72
    | ~ spl7_84
    | ~ spl7_91 ),
    inference(backward_demodulation,[],[f661,f856])).

fof(f856,plain,
    ( k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2)
    | ~ spl7_84
    | ~ spl7_91 ),
    inference(forward_demodulation,[],[f760,f731])).

fof(f731,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2)
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f730])).

fof(f730,plain,
    ( spl7_84
  <=> k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f760,plain,
    ( k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2))
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f759])).

fof(f759,plain,
    ( spl7_91
  <=> k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f661,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f660])).

fof(f660,plain,
    ( spl7_72
  <=> v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f892,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))
    | spl7_105 ),
    inference(avatar_component_clause,[],[f891])).

fof(f891,plain,
    ( spl7_105
  <=> v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f918,plain,
    ( ~ spl7_74
    | ~ spl7_84
    | ~ spl7_91
    | spl7_106 ),
    inference(avatar_contradiction_clause,[],[f917])).

fof(f917,plain,
    ( $false
    | ~ spl7_74
    | ~ spl7_84
    | ~ spl7_91
    | spl7_106 ),
    inference(resolution,[],[f895,f861])).

fof(f861,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2))
    | ~ spl7_74
    | ~ spl7_84
    | ~ spl7_91 ),
    inference(backward_demodulation,[],[f671,f856])).

fof(f671,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),sK2,sK5(sK0,sK1,sK2))
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f670])).

fof(f670,plain,
    ( spl7_74
  <=> v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),sK2,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f895,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2))
    | spl7_106 ),
    inference(avatar_component_clause,[],[f894])).

fof(f894,plain,
    ( spl7_106
  <=> v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f914,plain,
    ( ~ spl7_77
    | ~ spl7_84
    | ~ spl7_91
    | spl7_104 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | ~ spl7_77
    | ~ spl7_84
    | ~ spl7_91
    | spl7_104 ),
    inference(resolution,[],[f889,f862])).

fof(f862,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2))
    | ~ spl7_77
    | ~ spl7_84
    | ~ spl7_91 ),
    inference(backward_demodulation,[],[f686,f856])).

fof(f686,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)))
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f685])).

fof(f685,plain,
    ( spl7_77
  <=> v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f889,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2))
    | spl7_104 ),
    inference(avatar_component_clause,[],[f888])).

fof(f888,plain,
    ( spl7_104
  <=> v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f896,plain,
    ( ~ spl7_80
    | ~ spl7_79
    | ~ spl7_19
    | ~ spl7_68
    | ~ spl7_69
    | ~ spl7_100
    | ~ spl7_101
    | ~ spl7_102
    | ~ spl7_103
    | ~ spl7_104
    | ~ spl7_105
    | ~ spl7_106
    | spl7_78
    | spl7_67
    | ~ spl7_18
    | ~ spl7_70
    | ~ spl7_84
    | ~ spl7_91 ),
    inference(avatar_split_clause,[],[f863,f759,f730,f650,f134,f639,f709,f894,f891,f888,f885,f882,f879,f876,f645,f642,f140,f712,f715])).

fof(f715,plain,
    ( spl7_80
  <=> v2_pre_topc(sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f712,plain,
    ( spl7_79
  <=> l1_pre_topc(sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f140,plain,
    ( spl7_19
  <=> v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f642,plain,
    ( spl7_68
  <=> v1_funct_1(sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f645,plain,
    ( spl7_69
  <=> m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f709,plain,
    ( spl7_78
  <=> v2_struct_0(sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f639,plain,
    ( spl7_67
  <=> v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f134,plain,
    ( spl7_18
  <=> ! [X3,X4] :
        ( v2_struct_0(X3)
        | v5_pre_topc(X4,sK0,X3)
        | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK2),sK2,X3)
        | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK2))
        | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK1),sK1,X3)
        | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3))
        | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f650,plain,
    ( spl7_70
  <=> m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f863,plain,
    ( v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | ~ spl7_18
    | ~ spl7_70
    | ~ spl7_84
    | ~ spl7_91 ),
    inference(resolution,[],[f859,f135])).

fof(f135,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
        | v5_pre_topc(X4,sK0,X3)
        | v2_struct_0(X3)
        | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK2),sK2,X3)
        | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3))
        | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK2))
        | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK1),sK1,X3)
        | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3))
        | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f134])).

fof(f859,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ spl7_70
    | ~ spl7_84
    | ~ spl7_91 ),
    inference(backward_demodulation,[],[f651,f856])).

fof(f651,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f650])).

fof(f812,plain,(
    ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f811])).

fof(f811,plain,
    ( $false
    | ~ spl7_24 ),
    inference(resolution,[],[f158,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_tsep_1(X0,X1,X2)
              <~> ( ! [X3] :
                      ( ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                            & v5_pre_topc(X4,X0,X3)
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                            & v1_funct_1(X4) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                          | ~ m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                          | ~ v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                          | ~ v1_funct_1(k2_tmap_1(X0,X3,X4,X1))
                          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                          | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                          | ~ v1_funct_1(X4) )
                      | ~ l1_pre_topc(X3)
                      | ~ v2_pre_topc(X3)
                      | v2_struct_0(X3) )
                  & r1_tsep_1(X1,X2) ) )
              & k1_tsep_1(X0,X1,X2) = X0
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
               => ( k1_tsep_1(X0,X1,X2) = X0
                 => ( r3_tsep_1(X0,X1,X2)
                  <=> ( ! [X3] :
                          ( ( l1_pre_topc(X3)
                            & v2_pre_topc(X3)
                            & ~ v2_struct_0(X3) )
                         => ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) )
                             => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                  & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                  & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                  & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                  & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                               => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                  & v5_pre_topc(X4,X0,X3)
                                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                  & v1_funct_1(X4) ) ) ) )
                      & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
             => ( k1_tsep_1(X0,X1,X2) = X0
               => ( r3_tsep_1(X0,X1,X2)
                <=> ( ! [X3] :
                        ( ( l1_pre_topc(X3)
                          & v2_pre_topc(X3)
                          & ~ v2_struct_0(X3) )
                       => ! [X4] :
                            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                              & v1_funct_1(X4) )
                           => ( ( m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X2))
                                & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
                                & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3)
                                & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3))
                                & v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) )
                             => ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3))))
                                & v5_pre_topc(X4,X0,X3)
                                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3))
                                & v1_funct_1(X4) ) ) ) )
                    & r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_tmap_1)).

fof(f158,plain,
    ( v2_struct_0(sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_24
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f810,plain,(
    ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f809])).

fof(f809,plain,
    ( $false
    | ~ spl7_22 ),
    inference(resolution,[],[f152,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f152,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl7_22
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f775,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f774,f709,f163,f160,f157,f154,f151,f148,f65,f145,f62])).

fof(f62,plain,
    ( spl7_1
  <=> r3_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f145,plain,
    ( spl7_20
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f65,plain,
    ( spl7_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f148,plain,
    ( spl7_21
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f154,plain,
    ( spl7_23
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f160,plain,
    ( spl7_25
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f163,plain,
    ( spl7_26
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f774,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | ~ spl7_78 ),
    inference(resolution,[],[f710,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_tmap_1)).

fof(f710,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f709])).

fof(f773,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_80 ),
    inference(avatar_split_clause,[],[f772,f715,f163,f160,f157,f154,f151,f148,f65,f145,f62])).

fof(f772,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_80 ),
    inference(resolution,[],[f716,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f716,plain,
    ( ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | spl7_80 ),
    inference(avatar_component_clause,[],[f715])).

fof(f771,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_79 ),
    inference(avatar_split_clause,[],[f770,f712,f163,f160,f157,f154,f151,f148,f65,f145,f62])).

fof(f770,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_79 ),
    inference(resolution,[],[f713,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f713,plain,
    ( ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | spl7_79 ),
    inference(avatar_component_clause,[],[f712])).

fof(f765,plain,
    ( spl7_92
    | ~ spl7_19
    | ~ spl7_68
    | spl7_78
    | ~ spl7_79
    | ~ spl7_80
    | ~ spl7_41
    | ~ spl7_23
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f705,f645,f154,f334,f715,f712,f709,f642,f140,f763])).

fof(f334,plain,
    ( spl7_41
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f705,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl7_69 ),
    inference(resolution,[],[f689,f280])).

fof(f280,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ m1_pre_topc(sK1,X4)
      | ~ m1_pre_topc(X4,sK0)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X5))
      | k3_tmap_1(sK0,X5,X4,sK1,X3) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X5),X3,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f38,f39,f40,f254])).

fof(f254,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ m1_pre_topc(sK1,X4)
      | ~ m1_pre_topc(X4,sK0)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k3_tmap_1(sK0,X5,X4,sK1,X3) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X5),X3,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f42,f37])).

fof(f37,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f689,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f645])).

fof(f761,plain,
    ( spl7_91
    | ~ spl7_19
    | ~ spl7_68
    | spl7_78
    | ~ spl7_79
    | ~ spl7_80
    | ~ spl7_41
    | ~ spl7_21
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f704,f645,f148,f334,f715,f712,f709,f642,f140,f759])).

fof(f704,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2))
    | ~ spl7_69 ),
    inference(resolution,[],[f689,f279])).

fof(f279,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_pre_topc(sK2,X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | k3_tmap_1(sK0,X2,X1,sK2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(sK2)) ) ),
    inference(global_subsumption,[],[f38,f39,f40,f253])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ m1_pre_topc(sK2,X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k3_tmap_1(sK0,X2,X1,sK2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f42,f34])).

fof(f34,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f732,plain,
    ( spl7_84
    | ~ spl7_19
    | ~ spl7_68
    | ~ spl7_79
    | ~ spl7_80
    | spl7_78
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f696,f645,f709,f715,f712,f642,f140,f730])).

fof(f696,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2)
    | ~ spl7_69 ),
    inference(resolution,[],[f689,f219])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | k2_tmap_1(sK0,X1,X0,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) ) ),
    inference(global_subsumption,[],[f38,f39,f40,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k2_tmap_1(sK0,X1,X0,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f43,f34])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f728,plain,
    ( spl7_83
    | ~ spl7_19
    | ~ spl7_68
    | ~ spl7_79
    | ~ spl7_80
    | spl7_78
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f695,f645,f709,f715,f712,f642,f140,f726])).

fof(f695,plain,
    ( v2_struct_0(sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK5(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK5(sK0,sK1,sK2))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1)
    | ~ spl7_69 ),
    inference(resolution,[],[f689,f220])).

fof(f220,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | k2_tmap_1(sK0,X3,X2,sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X2,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f38,f39,f40,f184])).

fof(f184,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k2_tmap_1(sK0,X3,X2,sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X2,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f43,f37])).

fof(f692,plain,
    ( spl7_1
    | spl7_20
    | ~ spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | spl7_68 ),
    inference(avatar_split_clause,[],[f691,f642,f163,f160,f157,f154,f151,f148,f65,f145,f62])).

fof(f691,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2)
    | spl7_68 ),
    inference(resolution,[],[f643,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK6(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f643,plain,
    ( ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | spl7_68 ),
    inference(avatar_component_clause,[],[f642])).

fof(f690,plain,
    ( spl7_1
    | spl7_69 ),
    inference(avatar_split_clause,[],[f688,f645,f62])).

fof(f688,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f174])).

fof(f174,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f48,f35])).

fof(f35,plain,(
    sK0 = k1_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,
    ( r1_tsep_1(sK1,sK2)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f687,plain,
    ( spl7_1
    | spl7_77 ),
    inference(avatar_split_clause,[],[f683,f685,f62])).

fof(f683,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f171])).

fof(f171,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f53,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK6(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f682,plain,
    ( spl7_1
    | spl7_76 ),
    inference(avatar_split_clause,[],[f678,f680,f62])).

fof(f678,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f168])).

fof(f168,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f49,f35])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK6(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f677,plain,
    ( spl7_1
    | spl7_75 ),
    inference(avatar_split_clause,[],[f673,f675,f62])).

fof(f673,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),sK1,sK5(sK0,sK1,sK2))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f177])).

fof(f177,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),sK1,sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f51,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK6(X0,X1,X2)),X1,sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f672,plain,
    ( spl7_1
    | spl7_74 ),
    inference(avatar_split_clause,[],[f668,f670,f62])).

fof(f668,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),sK2,sK5(sK0,sK1,sK2))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f178])).

fof(f178,plain,
    ( v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),sK2,sK5(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f55,f35])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK6(X0,X1,X2)),X2,sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

% (11574)Refutation not found, incomplete strategy% (11574)------------------------------
% (11574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11574)Termination reason: Refutation not found, incomplete strategy
fof(f667,plain,
    ( spl7_1
    | spl7_73 ),
    inference(avatar_split_clause,[],[f663,f665,f62])).

% (11574)Memory used [KB]: 6780
% (11574)Time elapsed: 0.153 s
% (11574)------------------------------
% (11574)------------------------------
fof(f663,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f223])).

fof(f223,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK6(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f662,plain,
    ( spl7_1
    | spl7_72 ),
    inference(avatar_split_clause,[],[f658,f660,f62])).

fof(f658,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f224])).

fof(f224,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f54,f35])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK6(X0,X1,X2)),u1_struct_0(X2),u1_struct_0(sK5(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f657,plain,
    ( spl7_1
    | spl7_71 ),
    inference(avatar_split_clause,[],[f653,f655,f62])).

fof(f653,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f226])).

fof(f226,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f52,f35])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK6(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f652,plain,
    ( spl7_1
    | spl7_70 ),
    inference(avatar_split_clause,[],[f648,f650,f62])).

fof(f648,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f229])).

fof(f229,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f56,f35])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK6(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f647,plain,
    ( spl7_1
    | ~ spl7_67
    | ~ spl7_68
    | ~ spl7_69 ),
    inference(avatar_split_clause,[],[f637,f645,f642,f639,f62])).

fof(f637,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f138,f286])).

fof(f286,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | ~ v1_funct_1(sK6(sK0,sK1,sK2))
    | ~ v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f44,f35])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | ~ v1_funct_1(sK6(X0,X1,X2))
      | ~ v1_funct_2(sK6(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2)))
      | ~ v5_pre_topc(sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK5(X0,X1,X2))
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f138,plain,
    ( v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f137])).

fof(f137,plain,
    ( v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | r3_tsep_1(sK0,sK1,sK2) ),
    inference(superposition,[],[f47,f35])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK6(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ r1_tsep_1(X1,X2)
      | v2_struct_0(X0)
      | r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f636,plain,
    ( spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | ~ spl7_16
    | ~ spl7_15
    | ~ spl7_14
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_7
    | spl7_17
    | ~ spl7_6
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_10
    | ~ spl7_38
    | ~ spl7_42
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f634,f342,f337,f302,f99,f111,f107,f103,f83,f128,f87,f91,f95,f115,f119,f123,f70,f75,f79])).

fof(f79,plain,
    ( spl7_5
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f75,plain,
    ( spl7_4
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f70,plain,
    ( spl7_3
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f123,plain,
    ( spl7_16
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f119,plain,
    ( spl7_15
  <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f115,plain,
    ( spl7_14
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f95,plain,
    ( spl7_9
  <=> v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f91,plain,
    ( spl7_8
  <=> v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f87,plain,
    ( spl7_7
  <=> v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f128,plain,
    ( spl7_17
  <=> v5_pre_topc(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f83,plain,
    ( spl7_6
  <=> m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f103,plain,
    ( spl7_11
  <=> v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f107,plain,
    ( spl7_12
  <=> v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f111,plain,
    ( spl7_13
  <=> v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f99,plain,
    ( spl7_10
  <=> m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f302,plain,
    ( spl7_38
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | v5_pre_topc(X1,sK0,X0)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0)
        | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0)
        | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f337,plain,
    ( spl7_42
  <=> k2_tmap_1(sK0,sK3,sK4,sK2) = k3_tmap_1(sK0,sK3,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f342,plain,
    ( spl7_43
  <=> k2_tmap_1(sK0,sK3,sK4,sK1) = k3_tmap_1(sK0,sK3,sK0,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f634,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK0,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_38
    | ~ spl7_42
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f633,f343])).

fof(f343,plain,
    ( k2_tmap_1(sK0,sK3,sK4,sK1) = k3_tmap_1(sK0,sK3,sK0,sK1,sK4)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f342])).

fof(f633,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK0,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ spl7_38
    | ~ spl7_42
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f632,f343])).

fof(f632,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK0,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ spl7_38
    | ~ spl7_42
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f631,f343])).

fof(f631,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK0,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ v1_funct_2(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ spl7_38
    | ~ spl7_42
    | ~ spl7_43 ),
    inference(forward_demodulation,[],[f630,f343])).

fof(f630,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK4,sK0,sK3)
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ v5_pre_topc(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),sK1,sK3)
    | ~ v1_funct_2(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ v1_funct_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(superposition,[],[f303,f338])).

fof(f338,plain,
    ( k2_tmap_1(sK0,sK3,sK4,sK2) = k3_tmap_1(sK0,sK3,sK0,sK2,sK4)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f337])).

fof(f303,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | v5_pre_topc(X1,sK0,X0)
        | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0)
        | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1))
        | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0)
        | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) )
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f302])).

fof(f360,plain,(
    spl7_41 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | spl7_41 ),
    inference(resolution,[],[f353,f40])).

fof(f353,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_41 ),
    inference(resolution,[],[f335,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f335,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl7_41 ),
    inference(avatar_component_clause,[],[f334])).

fof(f344,plain,
    ( spl7_20
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_23
    | ~ spl7_41
    | spl7_43
    | ~ spl7_27
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f340,f275,f192,f342,f334,f154,f163,f160,f145])).

fof(f192,plain,
    ( spl7_27
  <=> ! [X4] :
        ( ~ m1_pre_topc(X4,sK0)
        | k2_tmap_1(sK0,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f275,plain,
    ( spl7_37
  <=> ! [X15,X14] :
        ( ~ m1_pre_topc(X14,sK0)
        | k3_tmap_1(X15,sK3,sK0,X14,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X14))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | ~ m1_pre_topc(sK0,X15)
        | ~ m1_pre_topc(X14,X15) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f340,plain,
    ( k2_tmap_1(sK0,sK3,sK4,sK1) = k3_tmap_1(sK0,sK3,sK0,sK1,sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_27
    | ~ spl7_37 ),
    inference(forward_demodulation,[],[f312,f238])).

fof(f238,plain,
    ( k2_tmap_1(sK0,sK3,sK4,sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(sK1))
    | ~ spl7_27 ),
    inference(resolution,[],[f193,f37])).

fof(f193,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK0)
        | k2_tmap_1(sK0,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X4)) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f192])).

fof(f312,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK3,sK0,sK1,sK4)
    | ~ spl7_37 ),
    inference(resolution,[],[f276,f37])).

fof(f276,plain,
    ( ! [X14,X15] :
        ( ~ m1_pre_topc(sK0,X15)
        | ~ m1_pre_topc(X14,sK0)
        | ~ m1_pre_topc(X14,X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X15)
        | k3_tmap_1(X15,sK3,sK0,X14,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X14)) )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f275])).

fof(f339,plain,
    ( spl7_20
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_21
    | ~ spl7_41
    | spl7_42
    | ~ spl7_27
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f332,f275,f192,f337,f334,f148,f163,f160,f145])).

fof(f332,plain,
    ( k2_tmap_1(sK0,sK3,sK4,sK2) = k3_tmap_1(sK0,sK3,sK0,sK2,sK4)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_27
    | ~ spl7_37 ),
    inference(forward_demodulation,[],[f311,f237])).

fof(f237,plain,
    ( k2_tmap_1(sK0,sK3,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(sK2))
    | ~ spl7_27 ),
    inference(resolution,[],[f193,f34])).

fof(f311,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK3,sK0,sK2,sK4)
    | ~ spl7_37 ),
    inference(resolution,[],[f276,f34])).

fof(f306,plain,
    ( ~ spl7_1
    | spl7_38 ),
    inference(avatar_split_clause,[],[f305,f302,f62])).

fof(f305,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0)
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0)
      | v5_pre_topc(X1,sK0,X0)
      | ~ r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(global_subsumption,[],[f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0)
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0)
      | v5_pre_topc(X1,sK0,X0)
      | ~ r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(global_subsumption,[],[f33,f36,f38,f39,f40,f34,f37,f293])).

fof(f293,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ m1_pre_topc(sK1,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0)
      | ~ v2_pre_topc(sK0)
      | ~ v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1))
      | ~ v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0)
      | v2_struct_0(sK0)
      | v5_pre_topc(X1,sK0,X0)
      | ~ r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(superposition,[],[f45,f35])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
      | ~ m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
      | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3))
      | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3)
      | ~ v2_pre_topc(X0)
      | ~ v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4))
      | ~ v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3))
      | ~ v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3)
      | v2_struct_0(X0)
      | v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3)
      | ~ r3_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f277,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | spl7_5
    | ~ spl7_3
    | ~ spl7_4
    | spl7_37
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f248,f115,f275,f75,f70,f79,f123,f119])).

fof(f248,plain,
    ( ! [X14,X15] :
        ( ~ m1_pre_topc(X14,sK0)
        | ~ m1_pre_topc(X14,X15)
        | ~ m1_pre_topc(sK0,X15)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X15)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
        | ~ v2_pre_topc(X15)
        | v2_struct_0(X15)
        | k3_tmap_1(X15,sK3,sK0,X14,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X14)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f42,f116])).

fof(f116,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f222,plain,(
    ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl7_20 ),
    inference(resolution,[],[f146,f38])).

fof(f146,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f145])).

fof(f194,plain,
    ( spl7_20
    | ~ spl7_26
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_3
    | ~ spl7_4
    | spl7_5
    | ~ spl7_25
    | spl7_27
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f180,f115,f192,f160,f79,f75,f70,f123,f119,f163,f145])).

fof(f180,plain,
    ( ! [X4] :
        ( ~ m1_pre_topc(X4,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK3)
        | ~ v2_pre_topc(sK3)
        | ~ l1_pre_topc(sK3)
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | k2_tmap_1(sK0,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X4)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f43,f116])).

fof(f176,plain,(
    spl7_23 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl7_23 ),
    inference(resolution,[],[f155,f37])).

fof(f155,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f154])).

fof(f173,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl7_21 ),
    inference(resolution,[],[f149,f34])).

fof(f149,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f148])).

fof(f170,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl7_26 ),
    inference(resolution,[],[f164,f39])).

fof(f164,plain,
    ( ~ v2_pre_topc(sK0)
    | spl7_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f167,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl7_25 ),
    inference(resolution,[],[f161,f40])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f160])).

fof(f165,plain,
    ( spl7_20
    | spl7_2
    | ~ spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_24
    | ~ spl7_25
    | ~ spl7_26
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f143,f62,f163,f160,f157,f154,f151,f148,f65,f145])).

fof(f143,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | r1_tsep_1(sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f63,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,
    ( r3_tsep_1(sK0,sK1,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f142,plain,
    ( spl7_1
    | spl7_19 ),
    inference(avatar_split_clause,[],[f138,f140,f62])).

fof(f136,plain,
    ( spl7_1
    | spl7_18 ),
    inference(avatar_split_clause,[],[f16,f134,f62])).

fof(f16,plain,(
    ! [X4,X3] :
      ( v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK1),sK1,X3)
      | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3))))
      | ~ v1_funct_1(k2_tmap_1(sK0,X3,X4,sK2))
      | ~ v1_funct_2(k2_tmap_1(sK0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK2),sK2,X3)
      | ~ m1_subset_1(k2_tmap_1(sK0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3))))
      | v5_pre_topc(X4,sK0,X3)
      | r3_tsep_1(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f132,plain,
    ( ~ spl7_1
    | ~ spl7_14
    | ~ spl7_17
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f17,f65,f123,f119,f128,f115,f62])).

fof(f17,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ v5_pre_topc(sK4,sK0,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f125,plain,
    ( ~ spl7_1
    | spl7_16
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f18,f65,f123,f62])).

fof(f18,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_1(sK4)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f121,plain,
    ( ~ spl7_1
    | spl7_15
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f19,f65,f119,f62])).

fof(f19,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f117,plain,
    ( ~ spl7_1
    | spl7_14
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f20,f65,f115,f62])).

fof(f20,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f113,plain,
    ( ~ spl7_1
    | spl7_13
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f21,f65,f111,f62])).

fof(f21,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f109,plain,
    ( ~ spl7_1
    | spl7_12
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f22,f65,f107,f62])).

fof(f22,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f105,plain,
    ( ~ spl7_1
    | spl7_11
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f23,f65,f103,f62])).

fof(f23,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f101,plain,
    ( ~ spl7_1
    | spl7_10
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f24,f65,f99,f62])).

fof(f24,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f97,plain,
    ( ~ spl7_1
    | spl7_9
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f25,f65,f95,f62])).

fof(f25,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f93,plain,
    ( ~ spl7_1
    | spl7_8
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f26,f65,f91,f62])).

fof(f26,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,
    ( ~ spl7_1
    | spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f27,f65,f87,f62])).

fof(f27,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f85,plain,
    ( ~ spl7_1
    | spl7_6
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f28,f65,f83,f62])).

fof(f28,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f81,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f29,f65,f79,f62])).

fof(f29,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | ~ v2_struct_0(sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,
    ( ~ spl7_1
    | spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f30,f65,f75,f62])).

fof(f30,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | v2_pre_topc(sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f73,plain,
    ( ~ spl7_1
    | spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f31,f65,f70,f62])).

fof(f31,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | l1_pre_topc(sK3)
    | ~ r3_tsep_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f32,f65,f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:21:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (11583)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (11575)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (11576)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (11587)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (11577)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (11569)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.52  % (11581)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (11584)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (11570)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.52  % (11570)Refutation not found, incomplete strategy% (11570)------------------------------
% 0.21/0.52  % (11570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11570)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11570)Memory used [KB]: 10618
% 0.21/0.52  % (11570)Time elapsed: 0.096 s
% 0.21/0.52  % (11570)------------------------------
% 0.21/0.52  % (11570)------------------------------
% 0.21/0.52  % (11573)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (11579)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (11574)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (11585)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (11568)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.53  % (11589)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.53  % (11588)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (11590)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.54  % (11580)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.54  % (11578)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.54  % (11584)Refutation not found, incomplete strategy% (11584)------------------------------
% 0.21/0.54  % (11584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11584)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11584)Memory used [KB]: 2174
% 0.21/0.54  % (11584)Time elapsed: 0.112 s
% 0.21/0.54  % (11584)------------------------------
% 0.21/0.54  % (11584)------------------------------
% 0.21/0.54  % (11571)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.54  % (11567)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.54  % (11582)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.55  % (11572)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.56  % (11586)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.58  % (11579)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f945,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f67,f73,f77,f81,f85,f89,f93,f97,f101,f105,f109,f113,f117,f121,f125,f132,f136,f142,f165,f167,f170,f173,f176,f194,f222,f277,f306,f339,f344,f360,f636,f647,f652,f657,f662,f667,f672,f677,f682,f687,f690,f692,f728,f732,f761,f765,f771,f773,f775,f810,f812,f896,f914,f918,f920,f927,f929,f931,f944])).
% 0.21/0.58  fof(f944,plain,(
% 0.21/0.58    ~spl7_71 | ~spl7_83 | ~spl7_92 | spl7_103),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f932])).
% 0.21/0.58  fof(f932,plain,(
% 0.21/0.58    $false | (~spl7_71 | ~spl7_83 | ~spl7_92 | spl7_103)),
% 0.21/0.58    inference(resolution,[],[f922,f886])).
% 0.21/0.58  fof(f886,plain,(
% 0.21/0.58    ~m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))))) | spl7_103),
% 0.21/0.58    inference(avatar_component_clause,[],[f885])).
% 0.21/0.58  fof(f885,plain,(
% 0.21/0.58    spl7_103 <=> m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).
% 0.21/0.58  fof(f922,plain,(
% 0.21/0.58    m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))))) | (~spl7_71 | ~spl7_83 | ~spl7_92)),
% 0.21/0.58    inference(backward_demodulation,[],[f656,f921])).
% 0.21/0.58  fof(f921,plain,(
% 0.21/0.58    k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1) | (~spl7_83 | ~spl7_92)),
% 0.21/0.58    inference(forward_demodulation,[],[f764,f727])).
% 0.21/0.58  fof(f727,plain,(
% 0.21/0.58    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1) | ~spl7_83),
% 0.21/0.58    inference(avatar_component_clause,[],[f726])).
% 0.21/0.58  fof(f726,plain,(
% 0.21/0.58    spl7_83 <=> k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).
% 0.21/0.58  fof(f764,plain,(
% 0.21/0.58    k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1)) | ~spl7_92),
% 0.21/0.58    inference(avatar_component_clause,[],[f763])).
% 0.21/0.58  fof(f763,plain,(
% 0.21/0.58    spl7_92 <=> k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).
% 0.21/0.58  fof(f656,plain,(
% 0.21/0.58    m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~spl7_71),
% 0.21/0.58    inference(avatar_component_clause,[],[f655])).
% 0.21/0.58  fof(f655,plain,(
% 0.21/0.58    spl7_71 <=> m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).
% 0.21/0.58  fof(f931,plain,(
% 0.21/0.58    ~spl7_73 | ~spl7_83 | ~spl7_92 | spl7_101),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f930])).
% 0.21/0.58  fof(f930,plain,(
% 0.21/0.58    $false | (~spl7_73 | ~spl7_83 | ~spl7_92 | spl7_101)),
% 0.21/0.58    inference(resolution,[],[f923,f880])).
% 0.21/0.58  fof(f880,plain,(
% 0.21/0.58    ~v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))) | spl7_101),
% 0.21/0.58    inference(avatar_component_clause,[],[f879])).
% 0.21/0.58  fof(f879,plain,(
% 0.21/0.58    spl7_101 <=> v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).
% 0.21/0.58  fof(f923,plain,(
% 0.21/0.58    v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))) | (~spl7_73 | ~spl7_83 | ~spl7_92)),
% 0.21/0.58    inference(backward_demodulation,[],[f666,f921])).
% 0.21/0.58  fof(f666,plain,(
% 0.21/0.58    v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))) | ~spl7_73),
% 0.21/0.58    inference(avatar_component_clause,[],[f665])).
% 0.21/0.58  fof(f665,plain,(
% 0.21/0.58    spl7_73 <=> v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).
% 0.21/0.58  fof(f929,plain,(
% 0.21/0.58    ~spl7_75 | ~spl7_83 | ~spl7_92 | spl7_102),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f928])).
% 0.21/0.58  fof(f928,plain,(
% 0.21/0.58    $false | (~spl7_75 | ~spl7_83 | ~spl7_92 | spl7_102)),
% 0.21/0.58    inference(resolution,[],[f924,f883])).
% 0.21/0.58  fof(f883,plain,(
% 0.21/0.58    ~v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2)) | spl7_102),
% 0.21/0.58    inference(avatar_component_clause,[],[f882])).
% 0.21/0.58  fof(f882,plain,(
% 0.21/0.58    spl7_102 <=> v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).
% 0.21/0.58  fof(f924,plain,(
% 0.21/0.58    v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2)) | (~spl7_75 | ~spl7_83 | ~spl7_92)),
% 0.21/0.58    inference(backward_demodulation,[],[f676,f921])).
% 0.21/0.58  fof(f676,plain,(
% 0.21/0.58    v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),sK1,sK5(sK0,sK1,sK2)) | ~spl7_75),
% 0.21/0.58    inference(avatar_component_clause,[],[f675])).
% 0.21/0.58  fof(f675,plain,(
% 0.21/0.58    spl7_75 <=> v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),sK1,sK5(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).
% 0.21/0.58  fof(f927,plain,(
% 0.21/0.58    ~spl7_76 | ~spl7_83 | ~spl7_92 | spl7_100),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f926])).
% 0.21/0.58  fof(f926,plain,(
% 0.21/0.58    $false | (~spl7_76 | ~spl7_83 | ~spl7_92 | spl7_100)),
% 0.21/0.58    inference(resolution,[],[f925,f877])).
% 0.21/0.58  fof(f877,plain,(
% 0.21/0.58    ~v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1)) | spl7_100),
% 0.21/0.58    inference(avatar_component_clause,[],[f876])).
% 0.21/0.58  fof(f876,plain,(
% 0.21/0.58    spl7_100 <=> v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).
% 0.21/0.58  fof(f925,plain,(
% 0.21/0.58    v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1)) | (~spl7_76 | ~spl7_83 | ~spl7_92)),
% 0.21/0.58    inference(backward_demodulation,[],[f681,f921])).
% 0.21/0.58  fof(f681,plain,(
% 0.21/0.58    v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2))) | ~spl7_76),
% 0.21/0.58    inference(avatar_component_clause,[],[f680])).
% 0.21/0.58  fof(f680,plain,(
% 0.21/0.58    spl7_76 <=> v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).
% 0.21/0.58  fof(f920,plain,(
% 0.21/0.58    ~spl7_72 | ~spl7_84 | ~spl7_91 | spl7_105),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f919])).
% 0.21/0.58  fof(f919,plain,(
% 0.21/0.58    $false | (~spl7_72 | ~spl7_84 | ~spl7_91 | spl7_105)),
% 0.21/0.58    inference(resolution,[],[f892,f860])).
% 0.21/0.58  fof(f860,plain,(
% 0.21/0.58    v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))) | (~spl7_72 | ~spl7_84 | ~spl7_91)),
% 0.21/0.58    inference(backward_demodulation,[],[f661,f856])).
% 0.21/0.58  fof(f856,plain,(
% 0.21/0.58    k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2) | (~spl7_84 | ~spl7_91)),
% 0.21/0.58    inference(forward_demodulation,[],[f760,f731])).
% 0.21/0.58  fof(f731,plain,(
% 0.21/0.58    k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2) | ~spl7_84),
% 0.21/0.58    inference(avatar_component_clause,[],[f730])).
% 0.21/0.58  fof(f730,plain,(
% 0.21/0.58    spl7_84 <=> k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).
% 0.21/0.58  fof(f760,plain,(
% 0.21/0.58    k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2)) | ~spl7_91),
% 0.21/0.58    inference(avatar_component_clause,[],[f759])).
% 0.21/0.58  fof(f759,plain,(
% 0.21/0.58    spl7_91 <=> k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).
% 0.21/0.58  fof(f661,plain,(
% 0.21/0.58    v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))) | ~spl7_72),
% 0.21/0.58    inference(avatar_component_clause,[],[f660])).
% 0.21/0.58  fof(f660,plain,(
% 0.21/0.58    spl7_72 <=> v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 0.21/0.58  fof(f892,plain,(
% 0.21/0.58    ~v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))) | spl7_105),
% 0.21/0.58    inference(avatar_component_clause,[],[f891])).
% 0.21/0.58  fof(f891,plain,(
% 0.21/0.58    spl7_105 <=> v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).
% 0.21/0.58  fof(f918,plain,(
% 0.21/0.58    ~spl7_74 | ~spl7_84 | ~spl7_91 | spl7_106),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f917])).
% 0.21/0.58  fof(f917,plain,(
% 0.21/0.58    $false | (~spl7_74 | ~spl7_84 | ~spl7_91 | spl7_106)),
% 0.21/0.58    inference(resolution,[],[f895,f861])).
% 0.21/0.58  fof(f861,plain,(
% 0.21/0.58    v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2)) | (~spl7_74 | ~spl7_84 | ~spl7_91)),
% 0.21/0.58    inference(backward_demodulation,[],[f671,f856])).
% 0.21/0.58  fof(f671,plain,(
% 0.21/0.58    v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),sK2,sK5(sK0,sK1,sK2)) | ~spl7_74),
% 0.21/0.58    inference(avatar_component_clause,[],[f670])).
% 0.21/0.58  fof(f670,plain,(
% 0.21/0.58    spl7_74 <=> v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),sK2,sK5(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).
% 0.21/0.58  fof(f895,plain,(
% 0.21/0.58    ~v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2)) | spl7_106),
% 0.21/0.58    inference(avatar_component_clause,[],[f894])).
% 0.21/0.58  fof(f894,plain,(
% 0.21/0.58    spl7_106 <=> v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).
% 0.21/0.58  fof(f914,plain,(
% 0.21/0.58    ~spl7_77 | ~spl7_84 | ~spl7_91 | spl7_104),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f913])).
% 0.21/0.58  fof(f913,plain,(
% 0.21/0.58    $false | (~spl7_77 | ~spl7_84 | ~spl7_91 | spl7_104)),
% 0.21/0.58    inference(resolution,[],[f889,f862])).
% 0.21/0.58  fof(f862,plain,(
% 0.21/0.58    v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2)) | (~spl7_77 | ~spl7_84 | ~spl7_91)),
% 0.21/0.58    inference(backward_demodulation,[],[f686,f856])).
% 0.21/0.58  fof(f686,plain,(
% 0.21/0.58    v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2))) | ~spl7_77),
% 0.21/0.58    inference(avatar_component_clause,[],[f685])).
% 0.21/0.58  fof(f685,plain,(
% 0.21/0.58    spl7_77 <=> v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).
% 0.21/0.58  fof(f889,plain,(
% 0.21/0.58    ~v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2)) | spl7_104),
% 0.21/0.58    inference(avatar_component_clause,[],[f888])).
% 0.21/0.58  fof(f888,plain,(
% 0.21/0.58    spl7_104 <=> v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).
% 0.21/0.58  fof(f896,plain,(
% 0.21/0.58    ~spl7_80 | ~spl7_79 | ~spl7_19 | ~spl7_68 | ~spl7_69 | ~spl7_100 | ~spl7_101 | ~spl7_102 | ~spl7_103 | ~spl7_104 | ~spl7_105 | ~spl7_106 | spl7_78 | spl7_67 | ~spl7_18 | ~spl7_70 | ~spl7_84 | ~spl7_91),
% 0.21/0.58    inference(avatar_split_clause,[],[f863,f759,f730,f650,f134,f639,f709,f894,f891,f888,f885,f882,f879,f876,f645,f642,f140,f712,f715])).
% 0.21/0.58  fof(f715,plain,(
% 0.21/0.58    spl7_80 <=> v2_pre_topc(sK5(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).
% 0.21/0.58  fof(f712,plain,(
% 0.21/0.58    spl7_79 <=> l1_pre_topc(sK5(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).
% 0.21/0.58  fof(f140,plain,(
% 0.21/0.58    spl7_19 <=> v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.58  fof(f642,plain,(
% 0.21/0.58    spl7_68 <=> v1_funct_1(sK6(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 0.21/0.58  fof(f645,plain,(
% 0.21/0.58    spl7_69 <=> m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).
% 0.21/0.58  fof(f709,plain,(
% 0.21/0.58    spl7_78 <=> v2_struct_0(sK5(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 0.21/0.58  fof(f639,plain,(
% 0.21/0.58    spl7_67 <=> v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).
% 0.21/0.58  fof(f134,plain,(
% 0.21/0.58    spl7_18 <=> ! [X3,X4] : (v2_struct_0(X3) | v5_pre_topc(X4,sK0,X3) | ~m1_subset_1(k2_tmap_1(sK0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK2),sK2,X3) | ~v1_funct_2(k2_tmap_1(sK0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(sK0,X3,X4,sK2)) | ~m1_subset_1(k2_tmap_1(sK0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK1),sK1,X3) | ~v1_funct_2(k2_tmap_1(sK0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(sK0,X3,X4,sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.58  fof(f650,plain,(
% 0.21/0.58    spl7_70 <=> m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2)))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).
% 0.21/0.58  fof(f863,plain,(
% 0.21/0.58    v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),sK2,sK5(sK0,sK1,sK2)) | ~v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))) | ~v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2)) | ~m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~v5_pre_topc(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),sK1,sK5(sK0,sK1,sK2)) | ~v1_funct_2(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))) | ~v1_funct_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1)) | ~m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~v1_funct_1(sK6(sK0,sK1,sK2)) | ~v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) | ~l1_pre_topc(sK5(sK0,sK1,sK2)) | ~v2_pre_topc(sK5(sK0,sK1,sK2)) | (~spl7_18 | ~spl7_70 | ~spl7_84 | ~spl7_91)),
% 0.21/0.58    inference(resolution,[],[f859,f135])).
% 0.21/0.58  fof(f135,plain,(
% 0.21/0.58    ( ! [X4,X3] : (~m1_subset_1(k2_tmap_1(sK0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | v5_pre_topc(X4,sK0,X3) | v2_struct_0(X3) | ~v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK2),sK2,X3) | ~v1_funct_2(k2_tmap_1(sK0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(sK0,X3,X4,sK2)) | ~m1_subset_1(k2_tmap_1(sK0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK1),sK1,X3) | ~v1_funct_2(k2_tmap_1(sK0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(sK0,X3,X4,sK1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3)) ) | ~spl7_18),
% 0.21/0.58    inference(avatar_component_clause,[],[f134])).
% 0.21/0.58  fof(f859,plain,(
% 0.21/0.58    m1_subset_1(k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))))) | (~spl7_70 | ~spl7_84 | ~spl7_91)),
% 0.21/0.58    inference(backward_demodulation,[],[f651,f856])).
% 0.21/0.58  fof(f651,plain,(
% 0.21/0.58    m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~spl7_70),
% 0.21/0.58    inference(avatar_component_clause,[],[f650])).
% 0.21/0.58  fof(f812,plain,(
% 0.21/0.58    ~spl7_24),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f811])).
% 0.21/0.58  fof(f811,plain,(
% 0.21/0.58    $false | ~spl7_24),
% 0.21/0.58    inference(resolution,[],[f158,f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ~v2_struct_0(sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : ((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) & k1_tsep_1(X0,X1,X2) = X0 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f7])).
% 0.21/0.58  fof(f7,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : (((r3_tsep_1(X0,X1,X2) <~> (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) | (~m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) | ~m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) | ~v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X0,X3,X4,X1)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) & k1_tsep_1(X0,X1,X2) = X0) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (k1_tsep_1(X0,X1,X2) = X0 => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2)))))))),
% 0.21/0.58    inference(negated_conjecture,[],[f5])).
% 0.21/0.58  fof(f5,conjecture,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (k1_tsep_1(X0,X1,X2) = X0 => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X2),X2,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X2),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X2)) & m1_subset_1(k2_tmap_1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k2_tmap_1(X0,X3,X4,X1),X1,X3) & v1_funct_2(k2_tmap_1(X0,X3,X4,X1),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k2_tmap_1(X0,X3,X4,X1))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X3)))) & v5_pre_topc(X4,X0,X3) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2)))))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_tmap_1)).
% 0.21/0.58  fof(f158,plain,(
% 0.21/0.58    v2_struct_0(sK1) | ~spl7_24),
% 0.21/0.58    inference(avatar_component_clause,[],[f157])).
% 0.21/0.58  fof(f157,plain,(
% 0.21/0.58    spl7_24 <=> v2_struct_0(sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.58  fof(f810,plain,(
% 0.21/0.58    ~spl7_22),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f809])).
% 0.21/0.58  fof(f809,plain,(
% 0.21/0.58    $false | ~spl7_22),
% 0.21/0.58    inference(resolution,[],[f152,f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ~v2_struct_0(sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f152,plain,(
% 0.21/0.58    v2_struct_0(sK2) | ~spl7_22),
% 0.21/0.58    inference(avatar_component_clause,[],[f151])).
% 0.21/0.58  fof(f151,plain,(
% 0.21/0.58    spl7_22 <=> v2_struct_0(sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.58  fof(f775,plain,(
% 0.21/0.58    spl7_1 | spl7_20 | ~spl7_2 | ~spl7_21 | spl7_22 | ~spl7_23 | spl7_24 | ~spl7_25 | ~spl7_26 | ~spl7_78),
% 0.21/0.58    inference(avatar_split_clause,[],[f774,f709,f163,f160,f157,f154,f151,f148,f65,f145,f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    spl7_1 <=> r3_tsep_1(sK0,sK1,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.58  fof(f145,plain,(
% 0.21/0.58    spl7_20 <=> v2_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    spl7_2 <=> r1_tsep_1(sK1,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.58  fof(f148,plain,(
% 0.21/0.58    spl7_21 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.58  fof(f154,plain,(
% 0.21/0.58    spl7_23 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.58  fof(f160,plain,(
% 0.21/0.58    spl7_25 <=> l1_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.58  fof(f163,plain,(
% 0.21/0.58    spl7_26 <=> v2_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.58  fof(f774,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2) | ~spl7_78),
% 0.21/0.58    inference(resolution,[],[f710,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v2_struct_0(sK5(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4)) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) & r1_tsep_1(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f14])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((r3_tsep_1(X0,X1,X2) <=> (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) | (~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~v1_funct_1(X4))) | (~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3))) & r1_tsep_1(X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r3_tsep_1(X0,X1,X2) <=> (! [X3] : ((l1_pre_topc(X3) & v2_pre_topc(X3) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4)) => ((m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) & m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) & v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) & v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) & v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4))) => (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) & v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) & v1_funct_1(X4))))) & r1_tsep_1(X1,X2))))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_tmap_1)).
% 0.21/0.58  fof(f710,plain,(
% 0.21/0.58    v2_struct_0(sK5(sK0,sK1,sK2)) | ~spl7_78),
% 0.21/0.58    inference(avatar_component_clause,[],[f709])).
% 0.21/0.58  fof(f773,plain,(
% 0.21/0.58    spl7_1 | spl7_20 | ~spl7_2 | ~spl7_21 | spl7_22 | ~spl7_23 | spl7_24 | ~spl7_25 | ~spl7_26 | spl7_80),
% 0.21/0.58    inference(avatar_split_clause,[],[f772,f715,f163,f160,f157,f154,f151,f148,f65,f145,f62])).
% 0.21/0.58  fof(f772,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2) | spl7_80),
% 0.21/0.58    inference(resolution,[],[f716,f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v2_pre_topc(sK5(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f716,plain,(
% 0.21/0.58    ~v2_pre_topc(sK5(sK0,sK1,sK2)) | spl7_80),
% 0.21/0.58    inference(avatar_component_clause,[],[f715])).
% 0.21/0.58  fof(f771,plain,(
% 0.21/0.58    spl7_1 | spl7_20 | ~spl7_2 | ~spl7_21 | spl7_22 | ~spl7_23 | spl7_24 | ~spl7_25 | ~spl7_26 | spl7_79),
% 0.21/0.58    inference(avatar_split_clause,[],[f770,f712,f163,f160,f157,f154,f151,f148,f65,f145,f62])).
% 0.21/0.58  fof(f770,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2) | spl7_79),
% 0.21/0.58    inference(resolution,[],[f713,f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (l1_pre_topc(sK5(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f713,plain,(
% 0.21/0.58    ~l1_pre_topc(sK5(sK0,sK1,sK2)) | spl7_79),
% 0.21/0.58    inference(avatar_component_clause,[],[f712])).
% 0.21/0.58  fof(f765,plain,(
% 0.21/0.58    spl7_92 | ~spl7_19 | ~spl7_68 | spl7_78 | ~spl7_79 | ~spl7_80 | ~spl7_41 | ~spl7_23 | ~spl7_69),
% 0.21/0.58    inference(avatar_split_clause,[],[f705,f645,f154,f334,f715,f712,f709,f642,f140,f763])).
% 0.21/0.58  fof(f334,plain,(
% 0.21/0.58    spl7_41 <=> m1_pre_topc(sK0,sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.21/0.58  fof(f705,plain,(
% 0.21/0.58    ~m1_pre_topc(sK1,sK0) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK5(sK0,sK1,sK2)) | ~l1_pre_topc(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v1_funct_1(sK6(sK0,sK1,sK2)) | ~v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) | k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1)) | ~spl7_69),
% 0.21/0.58    inference(resolution,[],[f689,f280])).
% 0.21/0.58  fof(f280,plain,(
% 0.21/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~m1_pre_topc(sK1,X4) | ~m1_pre_topc(X4,sK0) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X5) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X5)) | k3_tmap_1(sK0,X5,X4,sK1,X3) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X5),X3,u1_struct_0(sK1))) )),
% 0.21/0.58    inference(global_subsumption,[],[f38,f39,f40,f254])).
% 0.21/0.58  fof(f254,plain,(
% 0.21/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5)))) | ~m1_pre_topc(sK1,X4) | ~m1_pre_topc(X4,sK0) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | v2_struct_0(X5) | ~l1_pre_topc(sK0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X5)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k3_tmap_1(sK0,X5,X4,sK1,X3) = k2_partfun1(u1_struct_0(X4),u1_struct_0(X5),X3,u1_struct_0(sK1))) )),
% 0.21/0.58    inference(resolution,[],[f42,f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    m1_pre_topc(sK1,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f10])).
% 0.21/0.58  fof(f10,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    l1_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    v2_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ~v2_struct_0(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f689,plain,(
% 0.21/0.58    m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~spl7_69),
% 0.21/0.58    inference(avatar_component_clause,[],[f645])).
% 0.21/0.58  fof(f761,plain,(
% 0.21/0.58    spl7_91 | ~spl7_19 | ~spl7_68 | spl7_78 | ~spl7_79 | ~spl7_80 | ~spl7_41 | ~spl7_21 | ~spl7_69),
% 0.21/0.58    inference(avatar_split_clause,[],[f704,f645,f148,f334,f715,f712,f709,f642,f140,f759])).
% 0.21/0.58  fof(f704,plain,(
% 0.21/0.58    ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK0,sK0) | ~v2_pre_topc(sK5(sK0,sK1,sK2)) | ~l1_pre_topc(sK5(sK0,sK1,sK2)) | v2_struct_0(sK5(sK0,sK1,sK2)) | ~v1_funct_1(sK6(sK0,sK1,sK2)) | ~v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) | k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2)) | ~spl7_69),
% 0.21/0.58    inference(resolution,[],[f689,f279])).
% 0.21/0.58  fof(f279,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X1,sK0) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | k3_tmap_1(sK0,X2,X1,sK2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(sK2))) )),
% 0.21/0.58    inference(global_subsumption,[],[f38,f39,f40,f253])).
% 0.21/0.58  fof(f253,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(sK2,X1) | ~m1_pre_topc(X1,sK0) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k3_tmap_1(sK0,X2,X1,sK2,X0) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(sK2))) )),
% 0.21/0.58    inference(resolution,[],[f42,f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    m1_pre_topc(sK2,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f732,plain,(
% 0.21/0.58    spl7_84 | ~spl7_19 | ~spl7_68 | ~spl7_79 | ~spl7_80 | spl7_78 | ~spl7_69),
% 0.21/0.58    inference(avatar_split_clause,[],[f696,f645,f709,f715,f712,f642,f140,f730])).
% 0.21/0.58  fof(f696,plain,(
% 0.21/0.58    v2_struct_0(sK5(sK0,sK1,sK2)) | ~v2_pre_topc(sK5(sK0,sK1,sK2)) | ~l1_pre_topc(sK5(sK0,sK1,sK2)) | ~v1_funct_1(sK6(sK0,sK1,sK2)) | ~v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK2)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK2) | ~spl7_69),
% 0.21/0.58    inference(resolution,[],[f689,f219])).
% 0.21/0.58  fof(f219,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | k2_tmap_1(sK0,X1,X0,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2))) )),
% 0.21/0.58    inference(global_subsumption,[],[f38,f39,f40,f183])).
% 0.21/0.58  fof(f183,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,X1,X0,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X1),X0,u1_struct_0(sK2))) )),
% 0.21/0.58    inference(resolution,[],[f43,f34])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f12])).
% 0.21/0.58  fof(f12,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.21/0.58  fof(f728,plain,(
% 0.21/0.58    spl7_83 | ~spl7_19 | ~spl7_68 | ~spl7_79 | ~spl7_80 | spl7_78 | ~spl7_69),
% 0.21/0.58    inference(avatar_split_clause,[],[f695,f645,f709,f715,f712,f642,f140,f726])).
% 0.21/0.58  fof(f695,plain,(
% 0.21/0.58    v2_struct_0(sK5(sK0,sK1,sK2)) | ~v2_pre_topc(sK5(sK0,sK1,sK2)) | ~l1_pre_topc(sK5(sK0,sK1,sK2)) | ~v1_funct_1(sK6(sK0,sK1,sK2)) | ~v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2)),sK6(sK0,sK1,sK2),u1_struct_0(sK1)) = k2_tmap_1(sK0,sK5(sK0,sK1,sK2),sK6(sK0,sK1,sK2),sK1) | ~spl7_69),
% 0.21/0.58    inference(resolution,[],[f689,f220])).
% 0.21/0.58  fof(f220,plain,(
% 0.21/0.58    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | k2_tmap_1(sK0,X3,X2,sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X2,u1_struct_0(sK1))) )),
% 0.21/0.58    inference(global_subsumption,[],[f38,f39,f40,f184])).
% 0.21/0.58  fof(f184,plain,(
% 0.21/0.58    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~l1_pre_topc(sK0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X3)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,X3,X2,sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(X3),X2,u1_struct_0(sK1))) )),
% 0.21/0.58    inference(resolution,[],[f43,f37])).
% 0.21/0.58  fof(f692,plain,(
% 0.21/0.58    spl7_1 | spl7_20 | ~spl7_2 | ~spl7_21 | spl7_22 | ~spl7_23 | spl7_24 | ~spl7_25 | ~spl7_26 | spl7_68),
% 0.21/0.58    inference(avatar_split_clause,[],[f691,f642,f163,f160,f157,f154,f151,f148,f65,f145,f62])).
% 0.21/0.58  fof(f691,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2) | spl7_68),
% 0.21/0.58    inference(resolution,[],[f643,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v1_funct_1(sK6(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f15])).
% 0.21/0.58  fof(f643,plain,(
% 0.21/0.58    ~v1_funct_1(sK6(sK0,sK1,sK2)) | spl7_68),
% 0.21/0.58    inference(avatar_component_clause,[],[f642])).
% 0.21/0.58  fof(f690,plain,(
% 0.21/0.58    spl7_1 | spl7_69),
% 0.21/0.58    inference(avatar_split_clause,[],[f688,f645,f62])).
% 1.91/0.60  fof(f688,plain,(
% 1.91/0.60    m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))))) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f174])).
% 1.91/0.60  fof(f174,plain,(
% 1.91/0.60    m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(superposition,[],[f48,f35])).
% 1.91/0.60  fof(f35,plain,(
% 1.91/0.60    sK0 = k1_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(cnf_transformation,[],[f8])).
% 1.91/0.60  fof(f48,plain,(
% 1.91/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.60    inference(cnf_transformation,[],[f15])).
% 1.91/0.60  fof(f32,plain,(
% 1.91/0.60    r1_tsep_1(sK1,sK2) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(cnf_transformation,[],[f8])).
% 1.91/0.60  fof(f687,plain,(
% 1.91/0.60    spl7_1 | spl7_77),
% 1.91/0.60    inference(avatar_split_clause,[],[f683,f685,f62])).
% 1.91/0.60  fof(f683,plain,(
% 1.91/0.60    v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2))) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f171])).
% 1.91/0.60  fof(f171,plain,(
% 1.91/0.60    v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(superposition,[],[f53,f35])).
% 1.91/0.60  fof(f53,plain,(
% 1.91/0.60    ( ! [X2,X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK6(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.60    inference(cnf_transformation,[],[f15])).
% 1.91/0.60  fof(f682,plain,(
% 1.91/0.60    spl7_1 | spl7_76),
% 1.91/0.60    inference(avatar_split_clause,[],[f678,f680,f62])).
% 1.91/0.60  fof(f678,plain,(
% 1.91/0.60    v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2))) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f168])).
% 1.91/0.60  fof(f168,plain,(
% 1.91/0.60    v1_funct_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(superposition,[],[f49,f35])).
% 1.91/0.60  fof(f49,plain,(
% 1.91/0.60    ( ! [X2,X0,X1] : (v1_funct_1(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK6(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.60    inference(cnf_transformation,[],[f15])).
% 1.91/0.60  fof(f677,plain,(
% 1.91/0.60    spl7_1 | spl7_75),
% 1.91/0.60    inference(avatar_split_clause,[],[f673,f675,f62])).
% 1.91/0.60  fof(f673,plain,(
% 1.91/0.60    v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),sK1,sK5(sK0,sK1,sK2)) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f177])).
% 1.91/0.60  fof(f177,plain,(
% 1.91/0.60    v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),sK1,sK5(sK0,sK1,sK2)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(superposition,[],[f51,f35])).
% 1.91/0.60  fof(f51,plain,(
% 1.91/0.60    ( ! [X2,X0,X1] : (v5_pre_topc(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK6(X0,X1,X2)),X1,sK5(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.60    inference(cnf_transformation,[],[f15])).
% 1.91/0.60  fof(f672,plain,(
% 1.91/0.60    spl7_1 | spl7_74),
% 1.91/0.60    inference(avatar_split_clause,[],[f668,f670,f62])).
% 1.91/0.60  fof(f668,plain,(
% 1.91/0.60    v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),sK2,sK5(sK0,sK1,sK2)) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f178])).
% 1.91/0.60  fof(f178,plain,(
% 1.91/0.60    v5_pre_topc(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),sK2,sK5(sK0,sK1,sK2)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(superposition,[],[f55,f35])).
% 1.91/0.60  fof(f55,plain,(
% 1.91/0.60    ( ! [X2,X0,X1] : (v5_pre_topc(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK6(X0,X1,X2)),X2,sK5(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.60    inference(cnf_transformation,[],[f15])).
% 1.91/0.60  % (11574)Refutation not found, incomplete strategy% (11574)------------------------------
% 1.91/0.60  % (11574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.60  % (11574)Termination reason: Refutation not found, incomplete strategy
% 1.91/0.60  fof(f667,plain,(
% 1.91/0.60    spl7_1 | spl7_73),
% 1.91/0.60    inference(avatar_split_clause,[],[f663,f665,f62])).
% 1.91/0.60  
% 1.91/0.60  % (11574)Memory used [KB]: 6780
% 1.91/0.60  % (11574)Time elapsed: 0.153 s
% 1.91/0.60  % (11574)------------------------------
% 1.91/0.60  % (11574)------------------------------
% 1.91/0.60  fof(f663,plain,(
% 1.91/0.60    v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f223])).
% 1.91/0.60  fof(f223,plain,(
% 1.91/0.60    v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.60    inference(superposition,[],[f50,f35])).
% 1.91/0.60  fof(f50,plain,(
% 1.91/0.60    ( ! [X2,X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK6(X0,X1,X2)),u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.60    inference(cnf_transformation,[],[f15])).
% 1.91/0.60  fof(f662,plain,(
% 1.91/0.60    spl7_1 | spl7_72),
% 1.91/0.60    inference(avatar_split_clause,[],[f658,f660,f62])).
% 1.91/0.61  fof(f658,plain,(
% 1.91/0.61    v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f224])).
% 1.91/0.61  fof(f224,plain,(
% 1.91/0.61    v1_funct_2(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(superposition,[],[f54,f35])).
% 1.91/0.61  fof(f54,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (v1_funct_2(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK6(X0,X1,X2)),u1_struct_0(X2),u1_struct_0(sK5(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f15])).
% 1.91/0.61  fof(f657,plain,(
% 1.91/0.61    spl7_1 | spl7_71),
% 1.91/0.61    inference(avatar_split_clause,[],[f653,f655,f62])).
% 1.91/0.61  fof(f653,plain,(
% 1.91/0.61    m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))))) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f226])).
% 1.91/0.61  fof(f226,plain,(
% 1.91/0.61    m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK1,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(superposition,[],[f52,f35])).
% 1.91/0.61  fof(f52,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X1,sK6(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK5(X0,X1,X2))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f15])).
% 1.91/0.61  fof(f652,plain,(
% 1.91/0.61    spl7_1 | spl7_70),
% 1.91/0.61    inference(avatar_split_clause,[],[f648,f650,f62])).
% 1.91/0.61  fof(f648,plain,(
% 1.91/0.61    m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))))) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f229])).
% 1.91/0.61  fof(f229,plain,(
% 1.91/0.61    m1_subset_1(k3_tmap_1(sK0,sK5(sK0,sK1,sK2),sK0,sK2,sK6(sK0,sK1,sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(superposition,[],[f56,f35])).
% 1.91/0.61  fof(f56,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k3_tmap_1(X0,sK5(X0,X1,X2),k1_tsep_1(X0,X1,X2),X2,sK6(X0,X1,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK5(X0,X1,X2))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f15])).
% 1.91/0.61  fof(f647,plain,(
% 1.91/0.61    spl7_1 | ~spl7_67 | ~spl7_68 | ~spl7_69),
% 1.91/0.61    inference(avatar_split_clause,[],[f637,f645,f642,f639,f62])).
% 1.91/0.61  fof(f637,plain,(
% 1.91/0.61    ~m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~v1_funct_1(sK6(sK0,sK1,sK2)) | ~v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2)) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f138,f286])).
% 1.91/0.61  fof(f286,plain,(
% 1.91/0.61    ~m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | ~v1_funct_1(sK6(sK0,sK1,sK2)) | ~v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) | ~v5_pre_topc(sK6(sK0,sK1,sK2),sK0,sK5(sK0,sK1,sK2)) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(superposition,[],[f44,f35])).
% 1.91/0.61  fof(f44,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | ~v1_funct_1(sK6(X0,X1,X2)) | ~v1_funct_2(sK6(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2))) | ~v5_pre_topc(sK6(X0,X1,X2),k1_tsep_1(X0,X1,X2),sK5(X0,X1,X2)) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f15])).
% 1.91/0.61  fof(f138,plain,(
% 1.91/0.61    v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(global_subsumption,[],[f32,f33,f36,f38,f39,f40,f34,f37,f137])).
% 1.91/0.61  fof(f137,plain,(
% 1.91/0.61    v1_funct_2(sK6(sK0,sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK5(sK0,sK1,sK2))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(superposition,[],[f47,f35])).
% 1.91/0.61  fof(f47,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (v1_funct_2(sK6(X0,X1,X2),u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(sK5(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~r1_tsep_1(X1,X2) | v2_struct_0(X0) | r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f15])).
% 1.91/0.61  fof(f636,plain,(
% 1.91/0.61    spl7_5 | ~spl7_4 | ~spl7_3 | ~spl7_16 | ~spl7_15 | ~spl7_14 | ~spl7_9 | ~spl7_8 | ~spl7_7 | spl7_17 | ~spl7_6 | ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_10 | ~spl7_38 | ~spl7_42 | ~spl7_43),
% 1.91/0.61    inference(avatar_split_clause,[],[f634,f342,f337,f302,f99,f111,f107,f103,f83,f128,f87,f91,f95,f115,f119,f123,f70,f75,f79])).
% 1.91/0.61  fof(f79,plain,(
% 1.91/0.61    spl7_5 <=> v2_struct_0(sK3)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.91/0.61  fof(f75,plain,(
% 1.91/0.61    spl7_4 <=> v2_pre_topc(sK3)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.91/0.61  fof(f70,plain,(
% 1.91/0.61    spl7_3 <=> l1_pre_topc(sK3)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.91/0.61  fof(f123,plain,(
% 1.91/0.61    spl7_16 <=> v1_funct_1(sK4)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.91/0.61  fof(f119,plain,(
% 1.91/0.61    spl7_15 <=> v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.91/0.61  fof(f115,plain,(
% 1.91/0.61    spl7_14 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3))))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.91/0.61  fof(f95,plain,(
% 1.91/0.61    spl7_9 <=> v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.91/0.61  fof(f91,plain,(
% 1.91/0.61    spl7_8 <=> v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.91/0.61  fof(f87,plain,(
% 1.91/0.61    spl7_7 <=> v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.91/0.61  fof(f128,plain,(
% 1.91/0.61    spl7_17 <=> v5_pre_topc(sK4,sK0,sK3)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.91/0.61  fof(f83,plain,(
% 1.91/0.61    spl7_6 <=> m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.91/0.61  fof(f103,plain,(
% 1.91/0.61    spl7_11 <=> v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.91/0.61  fof(f107,plain,(
% 1.91/0.61    spl7_12 <=> v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.91/0.61  fof(f111,plain,(
% 1.91/0.61    spl7_13 <=> v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.91/0.61  fof(f99,plain,(
% 1.91/0.61    spl7_10 <=> m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3))))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.91/0.61  fof(f302,plain,(
% 1.91/0.61    spl7_38 <=> ! [X1,X0] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 1.91/0.61  fof(f337,plain,(
% 1.91/0.61    spl7_42 <=> k2_tmap_1(sK0,sK3,sK4,sK2) = k3_tmap_1(sK0,sK3,sK0,sK2,sK4)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 1.91/0.61  fof(f342,plain,(
% 1.91/0.61    spl7_43 <=> k2_tmap_1(sK0,sK3,sK4,sK1) = k3_tmap_1(sK0,sK3,sK0,sK1,sK4)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 1.91/0.61  fof(f634,plain,(
% 1.91/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3)) | ~v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3) | ~m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK0,sK3) | ~v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) | ~v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | (~spl7_38 | ~spl7_42 | ~spl7_43)),
% 1.91/0.61    inference(forward_demodulation,[],[f633,f343])).
% 1.91/0.61  fof(f343,plain,(
% 1.91/0.61    k2_tmap_1(sK0,sK3,sK4,sK1) = k3_tmap_1(sK0,sK3,sK0,sK1,sK4) | ~spl7_43),
% 1.91/0.61    inference(avatar_component_clause,[],[f342])).
% 1.91/0.61  fof(f633,plain,(
% 1.91/0.61    ~v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3)) | ~v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3) | ~m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK0,sK3) | ~v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) | ~v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_subset_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | (~spl7_38 | ~spl7_42 | ~spl7_43)),
% 1.91/0.61    inference(forward_demodulation,[],[f632,f343])).
% 1.91/0.61  fof(f632,plain,(
% 1.91/0.61    ~v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3)) | ~v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3) | ~m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK0,sK3) | ~v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) | ~v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) | ~v1_funct_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_subset_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | (~spl7_38 | ~spl7_42 | ~spl7_43)),
% 1.91/0.61    inference(forward_demodulation,[],[f631,f343])).
% 1.91/0.61  fof(f631,plain,(
% 1.91/0.61    ~v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3) | ~m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK0,sK3) | ~v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) | ~v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) | ~v1_funct_2(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_subset_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | (~spl7_38 | ~spl7_42 | ~spl7_43)),
% 1.91/0.61    inference(forward_demodulation,[],[f630,f343])).
% 1.91/0.61  fof(f630,plain,(
% 1.91/0.61    ~m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | v5_pre_topc(sK4,sK0,sK3) | ~v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) | ~v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) | ~v5_pre_topc(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),sK1,sK3) | ~v1_funct_2(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),u1_struct_0(sK1),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~m1_subset_1(k3_tmap_1(sK0,sK3,sK0,sK1,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | (~spl7_38 | ~spl7_42)),
% 1.91/0.61    inference(superposition,[],[f303,f338])).
% 1.91/0.61  fof(f338,plain,(
% 1.91/0.61    k2_tmap_1(sK0,sK3,sK4,sK2) = k3_tmap_1(sK0,sK3,sK0,sK2,sK4) | ~spl7_42),
% 1.91/0.61    inference(avatar_component_clause,[],[f337])).
% 1.91/0.61  fof(f303,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))) ) | ~spl7_38),
% 1.91/0.61    inference(avatar_component_clause,[],[f302])).
% 1.91/0.61  fof(f360,plain,(
% 1.91/0.61    spl7_41),
% 1.91/0.61    inference(avatar_contradiction_clause,[],[f359])).
% 1.91/0.61  fof(f359,plain,(
% 1.91/0.61    $false | spl7_41),
% 1.91/0.61    inference(resolution,[],[f353,f40])).
% 1.91/0.61  fof(f353,plain,(
% 1.91/0.61    ~l1_pre_topc(sK0) | spl7_41),
% 1.91/0.61    inference(resolution,[],[f335,f41])).
% 1.91/0.61  fof(f41,plain,(
% 1.91/0.61    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f9])).
% 1.91/0.61  fof(f9,plain,(
% 1.91/0.61    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.91/0.61    inference(ennf_transformation,[],[f4])).
% 1.91/0.61  fof(f4,axiom,(
% 1.91/0.61    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.91/0.61  fof(f335,plain,(
% 1.91/0.61    ~m1_pre_topc(sK0,sK0) | spl7_41),
% 1.91/0.61    inference(avatar_component_clause,[],[f334])).
% 1.91/0.61  fof(f344,plain,(
% 1.91/0.61    spl7_20 | ~spl7_25 | ~spl7_26 | ~spl7_23 | ~spl7_41 | spl7_43 | ~spl7_27 | ~spl7_37),
% 1.91/0.61    inference(avatar_split_clause,[],[f340,f275,f192,f342,f334,f154,f163,f160,f145])).
% 1.91/0.61  fof(f192,plain,(
% 1.91/0.61    spl7_27 <=> ! [X4] : (~m1_pre_topc(X4,sK0) | k2_tmap_1(sK0,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X4)))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.91/0.61  fof(f275,plain,(
% 1.91/0.61    spl7_37 <=> ! [X15,X14] : (~m1_pre_topc(X14,sK0) | k3_tmap_1(X15,sK3,sK0,X14,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X14)) | v2_struct_0(X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | ~m1_pre_topc(sK0,X15) | ~m1_pre_topc(X14,X15))),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 1.91/0.61  fof(f340,plain,(
% 1.91/0.61    k2_tmap_1(sK0,sK3,sK4,sK1) = k3_tmap_1(sK0,sK3,sK0,sK1,sK4) | ~m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_27 | ~spl7_37)),
% 1.91/0.61    inference(forward_demodulation,[],[f312,f238])).
% 1.91/0.61  fof(f238,plain,(
% 1.91/0.61    k2_tmap_1(sK0,sK3,sK4,sK1) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(sK1)) | ~spl7_27),
% 1.91/0.61    inference(resolution,[],[f193,f37])).
% 1.91/0.61  fof(f193,plain,(
% 1.91/0.61    ( ! [X4] : (~m1_pre_topc(X4,sK0) | k2_tmap_1(sK0,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X4))) ) | ~spl7_27),
% 1.91/0.61    inference(avatar_component_clause,[],[f192])).
% 1.91/0.61  fof(f312,plain,(
% 1.91/0.61    ~m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(sK1)) = k3_tmap_1(sK0,sK3,sK0,sK1,sK4) | ~spl7_37),
% 1.91/0.61    inference(resolution,[],[f276,f37])).
% 1.91/0.61  fof(f276,plain,(
% 1.91/0.61    ( ! [X14,X15] : (~m1_pre_topc(sK0,X15) | ~m1_pre_topc(X14,sK0) | ~m1_pre_topc(X14,X15) | ~v2_pre_topc(X15) | ~l1_pre_topc(X15) | v2_struct_0(X15) | k3_tmap_1(X15,sK3,sK0,X14,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X14))) ) | ~spl7_37),
% 1.91/0.61    inference(avatar_component_clause,[],[f275])).
% 1.91/0.61  fof(f339,plain,(
% 1.91/0.61    spl7_20 | ~spl7_25 | ~spl7_26 | ~spl7_21 | ~spl7_41 | spl7_42 | ~spl7_27 | ~spl7_37),
% 1.91/0.61    inference(avatar_split_clause,[],[f332,f275,f192,f337,f334,f148,f163,f160,f145])).
% 1.91/0.61  fof(f332,plain,(
% 1.91/0.61    k2_tmap_1(sK0,sK3,sK4,sK2) = k3_tmap_1(sK0,sK3,sK0,sK2,sK4) | ~m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl7_27 | ~spl7_37)),
% 1.91/0.61    inference(forward_demodulation,[],[f311,f237])).
% 1.91/0.61  fof(f237,plain,(
% 1.91/0.61    k2_tmap_1(sK0,sK3,sK4,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) | ~spl7_27),
% 1.91/0.61    inference(resolution,[],[f193,f34])).
% 1.91/0.61  fof(f311,plain,(
% 1.91/0.61    ~m1_pre_topc(sK0,sK0) | ~m1_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK3,sK0,sK2,sK4) | ~spl7_37),
% 1.91/0.61    inference(resolution,[],[f276,f34])).
% 1.91/0.61  fof(f306,plain,(
% 1.91/0.61    ~spl7_1 | spl7_38),
% 1.91/0.61    inference(avatar_split_clause,[],[f305,f302,f62])).
% 1.91/0.61  fof(f305,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0) | v5_pre_topc(X1,sK0,X0) | ~r3_tsep_1(sK0,sK1,sK2)) )),
% 1.91/0.61    inference(global_subsumption,[],[f300])).
% 1.91/0.61  fof(f300,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0) | v5_pre_topc(X1,sK0,X0) | ~r3_tsep_1(sK0,sK1,sK2)) )),
% 1.91/0.61    inference(global_subsumption,[],[f33,f36,f38,f39,f40,f34,f37,f293])).
% 1.91/0.61  fof(f293,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(sK0,X0,sK0,sK1,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK1,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK1,X1),u1_struct_0(sK1),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK1,X1),sK1,X0) | ~v2_pre_topc(sK0) | ~v1_funct_1(k3_tmap_1(sK0,X0,sK0,sK2,X1)) | ~v1_funct_2(k3_tmap_1(sK0,X0,sK0,sK2,X1),u1_struct_0(sK2),u1_struct_0(X0)) | ~v5_pre_topc(k3_tmap_1(sK0,X0,sK0,sK2,X1),sK2,X0) | v2_struct_0(sK0) | v5_pre_topc(X1,sK0,X0) | ~r3_tsep_1(sK0,sK1,sK2)) )),
% 1.91/0.61    inference(superposition,[],[f45,f35])).
% 1.91/0.61  fof(f45,plain,(
% 1.91/0.61    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) | ~m1_subset_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3)))) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4)) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),u1_struct_0(X1),u1_struct_0(X3)) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),X1,X3) | ~v2_pre_topc(X0) | ~v1_funct_1(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)) | ~v1_funct_2(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),u1_struct_0(X2),u1_struct_0(X3)) | ~v5_pre_topc(k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4),X2,X3) | v2_struct_0(X0) | v5_pre_topc(X4,k1_tsep_1(X0,X1,X2),X3) | ~r3_tsep_1(X0,X1,X2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f15])).
% 1.91/0.61  fof(f277,plain,(
% 1.91/0.61    ~spl7_15 | ~spl7_16 | spl7_5 | ~spl7_3 | ~spl7_4 | spl7_37 | ~spl7_14),
% 1.91/0.61    inference(avatar_split_clause,[],[f248,f115,f275,f75,f70,f79,f123,f119])).
% 1.91/0.61  fof(f248,plain,(
% 1.91/0.61    ( ! [X14,X15] : (~m1_pre_topc(X14,sK0) | ~m1_pre_topc(X14,X15) | ~m1_pre_topc(sK0,X15) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X15) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) | ~v2_pre_topc(X15) | v2_struct_0(X15) | k3_tmap_1(X15,sK3,sK0,X14,sK4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X14))) ) | ~spl7_14),
% 1.91/0.61    inference(resolution,[],[f42,f116])).
% 1.91/0.61  fof(f116,plain,(
% 1.91/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) | ~spl7_14),
% 1.91/0.61    inference(avatar_component_clause,[],[f115])).
% 1.91/0.61  fof(f222,plain,(
% 1.91/0.61    ~spl7_20),
% 1.91/0.61    inference(avatar_contradiction_clause,[],[f221])).
% 1.91/0.61  fof(f221,plain,(
% 1.91/0.61    $false | ~spl7_20),
% 1.91/0.61    inference(resolution,[],[f146,f38])).
% 1.91/0.61  fof(f146,plain,(
% 1.91/0.61    v2_struct_0(sK0) | ~spl7_20),
% 1.91/0.61    inference(avatar_component_clause,[],[f145])).
% 1.91/0.61  fof(f194,plain,(
% 1.91/0.61    spl7_20 | ~spl7_26 | ~spl7_15 | ~spl7_16 | ~spl7_3 | ~spl7_4 | spl7_5 | ~spl7_25 | spl7_27 | ~spl7_14),
% 1.91/0.61    inference(avatar_split_clause,[],[f180,f115,f192,f160,f79,f75,f70,f123,f119,f163,f145])).
% 1.91/0.61  fof(f180,plain,(
% 1.91/0.61    ( ! [X4] : (~m1_pre_topc(X4,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~v2_pre_topc(sK3) | ~l1_pre_topc(sK3) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK3),sK4,u1_struct_0(X4))) ) | ~spl7_14),
% 1.91/0.61    inference(resolution,[],[f43,f116])).
% 1.91/0.61  fof(f176,plain,(
% 1.91/0.61    spl7_23),
% 1.91/0.61    inference(avatar_contradiction_clause,[],[f175])).
% 1.91/0.61  fof(f175,plain,(
% 1.91/0.61    $false | spl7_23),
% 1.91/0.61    inference(resolution,[],[f155,f37])).
% 1.91/0.61  fof(f155,plain,(
% 1.91/0.61    ~m1_pre_topc(sK1,sK0) | spl7_23),
% 1.91/0.61    inference(avatar_component_clause,[],[f154])).
% 1.91/0.61  fof(f173,plain,(
% 1.91/0.61    spl7_21),
% 1.91/0.61    inference(avatar_contradiction_clause,[],[f172])).
% 1.91/0.61  fof(f172,plain,(
% 1.91/0.61    $false | spl7_21),
% 1.91/0.61    inference(resolution,[],[f149,f34])).
% 1.91/0.61  fof(f149,plain,(
% 1.91/0.61    ~m1_pre_topc(sK2,sK0) | spl7_21),
% 1.91/0.61    inference(avatar_component_clause,[],[f148])).
% 1.91/0.61  fof(f170,plain,(
% 1.91/0.61    spl7_26),
% 1.91/0.61    inference(avatar_contradiction_clause,[],[f169])).
% 1.91/0.61  fof(f169,plain,(
% 1.91/0.61    $false | spl7_26),
% 1.91/0.61    inference(resolution,[],[f164,f39])).
% 1.91/0.61  fof(f164,plain,(
% 1.91/0.61    ~v2_pre_topc(sK0) | spl7_26),
% 1.91/0.61    inference(avatar_component_clause,[],[f163])).
% 1.91/0.61  fof(f167,plain,(
% 1.91/0.61    spl7_25),
% 1.91/0.61    inference(avatar_contradiction_clause,[],[f166])).
% 1.91/0.61  fof(f166,plain,(
% 1.91/0.61    $false | spl7_25),
% 1.91/0.61    inference(resolution,[],[f161,f40])).
% 1.91/0.61  fof(f161,plain,(
% 1.91/0.61    ~l1_pre_topc(sK0) | spl7_25),
% 1.91/0.61    inference(avatar_component_clause,[],[f160])).
% 1.91/0.61  fof(f165,plain,(
% 1.91/0.61    spl7_20 | spl7_2 | ~spl7_21 | spl7_22 | ~spl7_23 | spl7_24 | ~spl7_25 | ~spl7_26 | ~spl7_1),
% 1.91/0.61    inference(avatar_split_clause,[],[f143,f62,f163,f160,f157,f154,f151,f148,f65,f145])).
% 1.91/0.61  fof(f143,plain,(
% 1.91/0.61    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(sK1,sK2) | v2_struct_0(sK0) | ~spl7_1),
% 1.91/0.61    inference(resolution,[],[f63,f60])).
% 1.91/0.61  fof(f60,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (~r3_tsep_1(X0,X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | r1_tsep_1(X1,X2) | v2_struct_0(X0)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f15])).
% 1.91/0.61  fof(f63,plain,(
% 1.91/0.61    r3_tsep_1(sK0,sK1,sK2) | ~spl7_1),
% 1.91/0.61    inference(avatar_component_clause,[],[f62])).
% 1.91/0.61  fof(f142,plain,(
% 1.91/0.61    spl7_1 | spl7_19),
% 1.91/0.61    inference(avatar_split_clause,[],[f138,f140,f62])).
% 1.91/0.61  fof(f136,plain,(
% 1.91/0.61    spl7_1 | spl7_18),
% 1.91/0.61    inference(avatar_split_clause,[],[f16,f134,f62])).
% 1.91/0.61  fof(f16,plain,(
% 1.91/0.61    ( ! [X4,X3] : (v2_struct_0(X3) | ~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X3)))) | ~v1_funct_1(k2_tmap_1(sK0,X3,X4,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,X3,X4,sK1),u1_struct_0(sK1),u1_struct_0(X3)) | ~v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK1),sK1,X3) | ~m1_subset_1(k2_tmap_1(sK0,X3,X4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X3)))) | ~v1_funct_1(k2_tmap_1(sK0,X3,X4,sK2)) | ~v1_funct_2(k2_tmap_1(sK0,X3,X4,sK2),u1_struct_0(sK2),u1_struct_0(X3)) | ~v5_pre_topc(k2_tmap_1(sK0,X3,X4,sK2),sK2,X3) | ~m1_subset_1(k2_tmap_1(sK0,X3,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X3)))) | v5_pre_topc(X4,sK0,X3) | r3_tsep_1(sK0,sK1,sK2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f132,plain,(
% 1.91/0.61    ~spl7_1 | ~spl7_14 | ~spl7_17 | ~spl7_15 | ~spl7_16 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f17,f65,f123,f119,f128,f115,f62])).
% 1.91/0.61  fof(f17,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) | ~v5_pre_topc(sK4,sK0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f125,plain,(
% 1.91/0.61    ~spl7_1 | spl7_16 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f18,f65,f123,f62])).
% 1.91/0.61  fof(f18,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | v1_funct_1(sK4) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f121,plain,(
% 1.91/0.61    ~spl7_1 | spl7_15 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f19,f65,f119,f62])).
% 1.91/0.61  fof(f19,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK3)) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f117,plain,(
% 1.91/0.61    ~spl7_1 | spl7_14 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f20,f65,f115,f62])).
% 1.91/0.61  fof(f20,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK3)))) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f113,plain,(
% 1.91/0.61    ~spl7_1 | spl7_13 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f21,f65,f111,f62])).
% 1.91/0.61  fof(f21,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK1)) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f109,plain,(
% 1.91/0.61    ~spl7_1 | spl7_12 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f22,f65,f107,f62])).
% 1.91/0.61  fof(f22,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK1),u1_struct_0(sK1),u1_struct_0(sK3)) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f105,plain,(
% 1.91/0.61    ~spl7_1 | spl7_11 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f23,f65,f103,f62])).
% 1.91/0.61  fof(f23,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK1),sK1,sK3) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f101,plain,(
% 1.91/0.61    ~spl7_1 | spl7_10 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f24,f65,f99,f62])).
% 1.91/0.61  fof(f24,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK3)))) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f97,plain,(
% 1.91/0.61    ~spl7_1 | spl7_9 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f25,f65,f95,f62])).
% 1.91/0.61  fof(f25,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | v1_funct_1(k2_tmap_1(sK0,sK3,sK4,sK2)) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f93,plain,(
% 1.91/0.61    ~spl7_1 | spl7_8 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f26,f65,f91,f62])).
% 1.91/0.61  fof(f26,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | v1_funct_2(k2_tmap_1(sK0,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f89,plain,(
% 1.91/0.61    ~spl7_1 | spl7_7 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f27,f65,f87,f62])).
% 1.91/0.61  fof(f27,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | v5_pre_topc(k2_tmap_1(sK0,sK3,sK4,sK2),sK2,sK3) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f85,plain,(
% 1.91/0.61    ~spl7_1 | spl7_6 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f28,f65,f83,f62])).
% 1.91/0.61  fof(f28,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | m1_subset_1(k2_tmap_1(sK0,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f81,plain,(
% 1.91/0.61    ~spl7_1 | ~spl7_5 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f29,f65,f79,f62])).
% 1.91/0.61  fof(f29,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | ~v2_struct_0(sK3) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f77,plain,(
% 1.91/0.61    ~spl7_1 | spl7_4 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f30,f65,f75,f62])).
% 1.91/0.61  fof(f30,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | v2_pre_topc(sK3) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f73,plain,(
% 1.91/0.61    ~spl7_1 | spl7_3 | ~spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f31,f65,f70,f62])).
% 1.91/0.61  fof(f31,plain,(
% 1.91/0.61    ~r1_tsep_1(sK1,sK2) | l1_pre_topc(sK3) | ~r3_tsep_1(sK0,sK1,sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f8])).
% 1.91/0.61  fof(f67,plain,(
% 1.91/0.61    spl7_1 | spl7_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f32,f65,f62])).
% 1.91/0.61  % SZS output end Proof for theBenchmark
% 1.91/0.61  % (11579)------------------------------
% 1.91/0.61  % (11579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.61  % (11579)Termination reason: Refutation
% 1.91/0.61  
% 1.91/0.61  % (11579)Memory used [KB]: 11769
% 1.91/0.61  % (11579)Time elapsed: 0.166 s
% 1.91/0.61  % (11579)------------------------------
% 1.91/0.61  % (11579)------------------------------
% 1.91/0.61  % (11566)Success in time 0.248 s
%------------------------------------------------------------------------------
