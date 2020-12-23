%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:32 EST 2020

% Result     : Theorem 12.55s
% Output     : Refutation 12.55s
% Verified   : 
% Statistics : Number of formulae       :  793 (2114 expanded)
%              Number of leaves         :  138 ( 891 expanded)
%              Depth                    :   27
%              Number of atoms          : 4123 (9895 expanded)
%              Number of equality atoms :  209 (1080 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13261,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f158,f163,f168,f173,f183,f188,f193,f198,f203,f208,f213,f218,f225,f231,f237,f245,f278,f284,f307,f328,f368,f459,f487,f501,f545,f583,f595,f637,f642,f672,f834,f835,f890,f900,f910,f1041,f1085,f1090,f1095,f1196,f1308,f1342,f1356,f1370,f1375,f1389,f1407,f1408,f1549,f1706,f1723,f1881,f1944,f3122,f3127,f3146,f3152,f3189,f3197,f3276,f3285,f3290,f3399,f3420,f3468,f3563,f3761,f3764,f4337,f4573,f4614,f4859,f5378,f5399,f5401,f5432,f5440,f5442,f5444,f5451,f5484,f5893,f6058,f6065,f6435,f6904,f6915,f7080,f7084,f7093,f7123,f7140,f7142,f7153,f7155,f7157,f7413,f7502,f7737,f7825,f7887,f7913,f7914,f7946,f7953,f8030,f8150,f8301,f8313,f8360,f8430,f8708,f9693,f9698,f9699,f9707,f9842,f10087,f10098,f10227,f10543,f12459,f12466,f13258])).

fof(f13258,plain,
    ( ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55
    | ~ spl6_63
    | spl6_69
    | ~ spl6_70
    | ~ spl6_413 ),
    inference(avatar_contradiction_clause,[],[f13257])).

fof(f13257,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55
    | ~ spl6_63
    | spl6_69
    | ~ spl6_70
    | ~ spl6_413 ),
    inference(subsumption_resolution,[],[f13256,f641])).

fof(f641,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f639])).

fof(f639,plain,
    ( spl6_55
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f13256,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55
    | ~ spl6_63
    | spl6_69
    | ~ spl6_70
    | ~ spl6_413 ),
    inference(forward_demodulation,[],[f13255,f592])).

fof(f592,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl6_52
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f13255,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55
    | ~ spl6_63
    | spl6_69
    | ~ spl6_70
    | ~ spl6_413 ),
    inference(subsumption_resolution,[],[f13254,f636])).

fof(f636,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f634])).

fof(f634,plain,
    ( spl6_54
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f13254,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_55
    | ~ spl6_63
    | spl6_69
    | ~ spl6_70
    | ~ spl6_413 ),
    inference(forward_demodulation,[],[f13253,f592])).

fof(f13253,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_55
    | ~ spl6_63
    | spl6_69
    | ~ spl6_70
    | ~ spl6_413 ),
    inference(subsumption_resolution,[],[f13252,f641])).

fof(f13252,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_63
    | spl6_69
    | ~ spl6_70
    | ~ spl6_413 ),
    inference(forward_demodulation,[],[f13251,f9690])).

fof(f9690,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_413 ),
    inference(avatar_component_clause,[],[f9688])).

fof(f9688,plain,
    ( spl6_413
  <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_413])])).

fof(f13251,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_63
    | spl6_69
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f13250,f592])).

fof(f13250,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_63
    | spl6_69
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f13249,f740])).

fof(f740,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | spl6_69 ),
    inference(avatar_component_clause,[],[f739])).

fof(f739,plain,
    ( spl6_69
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f13249,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_63
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f13248,f592])).

fof(f13248,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_63
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f13247,f681])).

fof(f681,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f679])).

fof(f679,plain,
    ( spl6_63
  <=> v1_partfun1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f13247,plain,
    ( ~ v1_partfun1(sK2,k1_relat_1(sK2))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_70 ),
    inference(forward_demodulation,[],[f13246,f592])).

fof(f13246,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f13245,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f13245,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f13244,f212])).

fof(f212,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f13244,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f13243,f207])).

fof(f207,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl6_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f13243,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f13242,f202])).

fof(f202,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_11
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f13242,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f13241,f197])).

fof(f197,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f13241,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f13240,f192])).

fof(f192,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f13240,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_1
    | ~ spl6_22
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f13229,f151])).

fof(f151,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl6_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f13229,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_22
    | ~ spl6_70 ),
    inference(resolution,[],[f9761,f147])).

fof(f147,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f9761,plain,
    ( ! [X1] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,u1_pre_topc(sK0))),u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X1)
        | ~ v4_relat_1(sK2,X1) )
    | ~ spl6_22
    | ~ spl6_70 ),
    inference(subsumption_resolution,[],[f9747,f277])).

fof(f277,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl6_22
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f9747,plain,
    ( ! [X1] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,u1_pre_topc(sK0))),u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X1)
        | ~ v4_relat_1(sK2,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_70 ),
    inference(superposition,[],[f744,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f744,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f743])).

fof(f743,plain,
    ( spl6_70
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f12466,plain,
    ( ~ spl6_56
    | spl6_2
    | ~ spl6_3
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f12465,f590,f160,f154,f644])).

fof(f644,plain,
    ( spl6_56
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f154,plain,
    ( spl6_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f160,plain,
    ( spl6_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f12465,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_3
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f12464,f162])).

fof(f162,plain,
    ( sK2 = sK3
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f160])).

fof(f12464,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f156,f592])).

fof(f156,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f154])).

fof(f12459,plain,
    ( spl6_1
    | ~ spl6_64
    | ~ spl6_62
    | ~ spl6_69
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f12458,f639,f634,f590,f275,f210,f205,f200,f195,f190,f739,f674,f684,f150])).

fof(f684,plain,
    ( spl6_64
  <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f674,plain,
    ( spl6_62
  <=> v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f12458,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f12457,f212])).

fof(f12457,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f12456,f207])).

fof(f12456,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f12455,f641])).

fof(f12455,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f12407,f636])).

fof(f12407,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_54
    | ~ spl6_55 ),
    inference(superposition,[],[f8958,f592])).

fof(f8958,plain,
    ( ! [X5] :
        ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1)
        | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | v5_pre_topc(sK2,X5,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_54
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f8957,f7902])).

fof(f7902,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl6_22
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f7901,f277])).

fof(f7901,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,X0,u1_struct_0(sK1))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_55 ),
    inference(superposition,[],[f641,f107])).

fof(f8957,plain,
    ( ! [X5] :
        ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1)
        | v5_pre_topc(sK2,X5,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1))
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f8956,f202])).

fof(f8956,plain,
    ( ! [X5] :
        ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1)
        | v5_pre_topc(sK2,X5,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1))
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f8955,f197])).

fof(f8955,plain,
    ( ! [X5] :
        ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1)
        | v5_pre_topc(sK2,X5,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f8947,f192])).

fof(f8947,plain,
    ( ! [X5] :
        ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | ~ v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
        | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1)
        | v5_pre_topc(sK2,X5,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(X5)
        | ~ v2_pre_topc(X5) )
    | ~ spl6_22
    | ~ spl6_54 ),
    inference(resolution,[],[f7929,f148])).

fof(f148,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f7929,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0) )
    | ~ spl6_22
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f7924,f277])).

fof(f7924,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ v1_partfun1(sK2,X0)
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_54 ),
    inference(superposition,[],[f636,f107])).

fof(f10543,plain,
    ( ~ spl6_228
    | spl6_40
    | spl6_232 ),
    inference(avatar_split_clause,[],[f10540,f3393,f484,f3323])).

fof(f3323,plain,
    ( spl6_228
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_228])])).

fof(f484,plain,
    ( spl6_40
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f3393,plain,
    ( spl6_232
  <=> u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_232])])).

fof(f10540,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl6_40
    | spl6_232 ),
    inference(subsumption_resolution,[],[f10537,f485])).

fof(f485,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_40 ),
    inference(avatar_component_clause,[],[f484])).

fof(f10537,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl6_232 ),
    inference(trivial_inequality_removal,[],[f10535])).

fof(f10535,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl6_232 ),
    inference(superposition,[],[f3394,f463])).

fof(f463,plain,(
    ! [X2,X1] :
      ( k1_relset_1(X1,X2,k1_xboole_0) = X1
      | k1_xboole_0 = X2
      | ~ v1_funct_2(k1_xboole_0,X1,X2) ) ),
    inference(resolution,[],[f94,f118])).

fof(f118,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f3394,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0)
    | spl6_232 ),
    inference(avatar_component_clause,[],[f3393])).

fof(f10227,plain,
    ( spl6_56
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f10226,f590,f160,f154,f644])).

fof(f10226,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f10225,f162])).

fof(f10225,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f155,f592])).

fof(f155,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f154])).

fof(f10098,plain,
    ( spl6_69
    | ~ spl6_56
    | ~ spl6_398
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_54
    | ~ spl6_55
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(avatar_split_clause,[],[f10097,f9688,f699,f694,f654,f639,f634,f200,f195,f190,f8930,f644,f739])).

fof(f8930,plain,
    ( spl6_398
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_398])])).

fof(f654,plain,
    ( spl6_58
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f694,plain,
    ( spl6_66
  <=> v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f699,plain,
    ( spl6_67
  <=> l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f10097,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_54
    | ~ spl6_55
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(subsumption_resolution,[],[f10096,f641])).

fof(f10096,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_54
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(forward_demodulation,[],[f10095,f9690])).

fof(f10095,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_54
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(subsumption_resolution,[],[f10094,f636])).

fof(f10094,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(forward_demodulation,[],[f10093,f9690])).

fof(f10093,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(forward_demodulation,[],[f10092,f9690])).

fof(f10092,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f10091,f696])).

fof(f696,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f694])).

fof(f10091,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f10090,f700])).

fof(f700,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f699])).

fof(f10090,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f10089,f202])).

fof(f10089,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f10088,f197])).

fof(f10088,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f8314,f192])).

fof(f8314,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_58 ),
    inference(resolution,[],[f656,f146])).

fof(f146,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f656,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f654])).

fof(f10087,plain,
    ( spl6_56
    | ~ spl6_69
    | ~ spl6_398
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_54
    | ~ spl6_55
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(avatar_split_clause,[],[f10086,f9688,f699,f694,f654,f639,f634,f200,f195,f190,f8930,f739,f644])).

fof(f10086,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_54
    | ~ spl6_55
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(subsumption_resolution,[],[f10085,f641])).

fof(f10085,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_54
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(forward_demodulation,[],[f10084,f9690])).

fof(f10084,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_54
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(subsumption_resolution,[],[f10083,f636])).

fof(f10083,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(forward_demodulation,[],[f10082,f9690])).

fof(f10082,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67
    | ~ spl6_413 ),
    inference(forward_demodulation,[],[f10081,f9690])).

fof(f10081,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58
    | ~ spl6_66
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f10080,f696])).

fof(f10080,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f10079,f700])).

fof(f10079,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f10078,f202])).

fof(f10078,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f10077,f197])).

fof(f10077,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f8315,f192])).

fof(f8315,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_58 ),
    inference(resolution,[],[f656,f145])).

fof(f145,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f9842,plain,
    ( spl6_398
    | ~ spl6_57
    | ~ spl6_413 ),
    inference(avatar_split_clause,[],[f9762,f9688,f649,f8930])).

fof(f649,plain,
    ( spl6_57
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f9762,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_57
    | ~ spl6_413 ),
    inference(backward_demodulation,[],[f651,f9690])).

fof(f651,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f649])).

fof(f9707,plain,
    ( spl6_64
    | ~ spl6_34
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f9706,f590,f448,f684])).

fof(f448,plain,
    ( spl6_34
  <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f9706,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ spl6_34
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f450,f592])).

fof(f450,plain,
    ( v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f448])).

fof(f9699,plain,
    ( k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f9698,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f9693,plain,
    ( spl6_413
    | ~ spl6_58
    | ~ spl6_72 ),
    inference(avatar_split_clause,[],[f9692,f817,f654,f9688])).

fof(f817,plain,
    ( spl6_72
  <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f9692,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_58
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f9683,f656])).

fof(f9683,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_72 ),
    inference(superposition,[],[f100,f819])).

fof(f819,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f817])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f8708,plain,
    ( spl6_72
    | spl6_40
    | ~ spl6_57
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f8707,f654,f649,f484,f817])).

fof(f8707,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl6_57
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f8690,f651])).

fof(f8690,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl6_58 ),
    inference(resolution,[],[f656,f94])).

fof(f8430,plain,
    ( ~ spl6_40
    | ~ spl6_58
    | spl6_73 ),
    inference(avatar_contradiction_clause,[],[f8429])).

fof(f8429,plain,
    ( $false
    | ~ spl6_40
    | ~ spl6_58
    | spl6_73 ),
    inference(subsumption_resolution,[],[f8428,f883])).

fof(f883,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_73 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl6_73
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f8428,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_40
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f8362,f140])).

fof(f140,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f8362,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl6_40
    | ~ spl6_58 ),
    inference(backward_demodulation,[],[f656,f486])).

fof(f486,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f484])).

fof(f8360,plain,
    ( spl6_62
    | ~ spl6_27
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f8359,f590,f325,f674])).

fof(f325,plain,
    ( spl6_27
  <=> v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f8359,plain,
    ( v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))
    | ~ spl6_27
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f327,f592])).

fof(f327,plain,
    ( v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f325])).

fof(f8313,plain,
    ( spl6_58
    | ~ spl6_17
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f8312,f590,f234,f654])).

fof(f234,plain,
    ( spl6_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f8312,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_17
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f236,f592])).

fof(f236,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f234])).

fof(f8301,plain,
    ( spl6_57
    | ~ spl6_16
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f8300,f590,f228,f649])).

fof(f228,plain,
    ( spl6_16
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f8300,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_16
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f230,f592])).

fof(f230,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f228])).

fof(f8150,plain,
    ( spl6_67
    | ~ spl6_12
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f8149,f590,f205,f699])).

fof(f8149,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_12
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f7996,f207])).

fof(f7996,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_52 ),
    inference(superposition,[],[f292,f592])).

fof(f292,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f111,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f111,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f8030,plain,
    ( spl6_66
    | ~ spl6_42
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f7961,f590,f513,f694])).

fof(f513,plain,
    ( spl6_42
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f7961,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_42
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f514,f592])).

fof(f514,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f513])).

fof(f7953,plain,
    ( spl6_77
    | ~ spl6_36
    | ~ spl6_104
    | spl6_110 ),
    inference(avatar_split_clause,[],[f7952,f1255,f1178,f457,f902])).

fof(f902,plain,
    ( spl6_77
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f457,plain,
    ( spl6_36
  <=> ! [X1,X2] :
        ( ~ v1_funct_2(k1_xboole_0,X1,X2)
        | v1_xboole_0(X2)
        | v1_partfun1(k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f1178,plain,
    ( spl6_104
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f1255,plain,
    ( spl6_110
  <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f7952,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_36
    | ~ spl6_104
    | spl6_110 ),
    inference(subsumption_resolution,[],[f7951,f1256])).

fof(f1256,plain,
    ( ~ v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | spl6_110 ),
    inference(avatar_component_clause,[],[f1255])).

fof(f7951,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_36
    | ~ spl6_104 ),
    inference(resolution,[],[f1180,f458])).

fof(f458,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(k1_xboole_0,X1,X2)
        | v1_xboole_0(X2)
        | v1_partfun1(k1_xboole_0,X1) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f457])).

fof(f1180,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f1178])).

fof(f7946,plain,
    ( spl6_63
    | ~ spl6_22
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f7945,f669,f275,f679])).

fof(f669,plain,
    ( spl6_61
  <=> v4_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f7945,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ spl6_22
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f7943,f277])).

fof(f7943,plain,
    ( v1_partfun1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_61 ),
    inference(resolution,[],[f671,f144])).

fof(f144,plain,(
    ! [X1] :
      ( ~ v4_relat_1(X1,k1_relat_1(X1))
      | v1_partfun1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f671,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f669])).

fof(f7914,plain,
    ( spl6_26
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f7907,f180,f320])).

fof(f320,plain,
    ( spl6_26
  <=> v4_relat_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f180,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f7907,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl6_7 ),
    inference(resolution,[],[f182,f127])).

fof(f182,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f180])).

fof(f7913,plain,
    ( spl6_37
    | spl6_38
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f7912,f185,f180,f474,f470])).

fof(f470,plain,
    ( spl6_37
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f474,plain,
    ( spl6_38
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f185,plain,
    ( spl6_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f7912,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f7904,f187])).

fof(f187,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f185])).

fof(f7904,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f182,f94])).

fof(f7887,plain,
    ( ~ spl6_85
    | ~ spl6_3
    | spl6_96 ),
    inference(avatar_split_clause,[],[f7886,f1118,f160,f991])).

fof(f991,plain,
    ( spl6_85
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f1118,plain,
    ( spl6_96
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f7886,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_3
    | spl6_96 ),
    inference(superposition,[],[f1119,f162])).

fof(f1119,plain,
    ( k1_xboole_0 != sK3
    | spl6_96 ),
    inference(avatar_component_clause,[],[f1118])).

fof(f7825,plain,
    ( ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_41
    | ~ spl6_95
    | ~ spl6_97
    | spl6_111
    | ~ spl6_230 ),
    inference(avatar_contradiction_clause,[],[f7824])).

fof(f7824,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_41
    | ~ spl6_95
    | ~ spl6_97
    | spl6_111
    | ~ spl6_230 ),
    inference(subsumption_resolution,[],[f7823,f1127])).

fof(f1127,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f1125])).

fof(f1125,plain,
    ( spl6_97
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f7823,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_41
    | ~ spl6_95
    | spl6_111
    | ~ spl6_230 ),
    inference(subsumption_resolution,[],[f7822,f1115])).

fof(f1115,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f1113,plain,
    ( spl6_95
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f7822,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_41
    | spl6_111
    | ~ spl6_230 ),
    inference(subsumption_resolution,[],[f7821,f207])).

fof(f7821,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_41
    | spl6_111
    | ~ spl6_230 ),
    inference(subsumption_resolution,[],[f7819,f212])).

fof(f7819,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_41
    | spl6_111
    | ~ spl6_230 ),
    inference(resolution,[],[f7815,f1294])).

fof(f1294,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_111 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f1293,plain,
    ( spl6_111
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f7815,plain,
    ( ! [X25] :
        ( v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ v5_pre_topc(k1_xboole_0,X25,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_41
    | ~ spl6_230 ),
    inference(duplicate_literal_removal,[],[f7814])).

fof(f7814,plain,
    ( ! [X25] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X25,sK1)
        | v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_41
    | ~ spl6_230 ),
    inference(forward_demodulation,[],[f7298,f3362])).

fof(f3362,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_230 ),
    inference(avatar_component_clause,[],[f3360])).

fof(f3360,plain,
    ( spl6_230
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_230])])).

fof(f7298,plain,
    ( ! [X25] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X25),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X25,sK1)
        | v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f7297,f197])).

fof(f7297,plain,
    ( ! [X25] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X25),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X25,sK1)
        | v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) )
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f7214,f202])).

fof(f7214,plain,
    ( ! [X25] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X25),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X25,sK1)
        | v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) )
    | ~ spl6_38
    | ~ spl6_41 ),
    inference(superposition,[],[f500,f476])).

fof(f476,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f474])).

fof(f500,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v5_pre_topc(k1_xboole_0,X1,X2)
        | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl6_41
  <=> ! [X1,X2] :
        ( ~ v5_pre_topc(k1_xboole_0,X1,X2)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
        | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f7737,plain,
    ( ~ spl6_321
    | ~ spl6_103
    | spl6_133 ),
    inference(avatar_split_clause,[],[f7736,f1718,f1166,f6055])).

fof(f6055,plain,
    ( spl6_321
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_321])])).

fof(f1166,plain,
    ( spl6_103
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f1718,plain,
    ( spl6_133
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).

fof(f7736,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_103
    | spl6_133 ),
    inference(forward_demodulation,[],[f1719,f1168])).

fof(f1168,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_103 ),
    inference(avatar_component_clause,[],[f1166])).

fof(f1719,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0)
    | spl6_133 ),
    inference(avatar_component_clause,[],[f1718])).

fof(f7502,plain,
    ( spl6_322
    | ~ spl6_104
    | ~ spl6_230 ),
    inference(avatar_split_clause,[],[f7456,f3360,f1178,f6062])).

fof(f6062,plain,
    ( spl6_322
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_322])])).

fof(f7456,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_104
    | ~ spl6_230 ),
    inference(backward_demodulation,[],[f1180,f3362])).

fof(f7413,plain,
    ( spl6_217
    | ~ spl6_103 ),
    inference(avatar_split_clause,[],[f7412,f1166,f3097])).

fof(f3097,plain,
    ( spl6_217
  <=> ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_217])])).

fof(f7412,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f7406,f118])).

fof(f7406,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X1) )
    | ~ spl6_103 ),
    inference(trivial_inequality_removal,[],[f7404])).

fof(f7404,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X1) )
    | ~ spl6_103 ),
    inference(superposition,[],[f418,f1168])).

fof(f418,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f417])).

fof(f417,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f416,f141])).

fof(f141,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f416,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f415,f100])).

fof(f415,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f138,f141])).

fof(f138,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f7157,plain,
    ( spl6_95
    | ~ spl6_1
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f7156,f991,f150,f1113])).

fof(f7156,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_1
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f151,f993])).

fof(f993,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f991])).

fof(f7155,plain,
    ( ~ spl6_219
    | spl6_2
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f7154,f1118,f154,f3223])).

fof(f3223,plain,
    ( spl6_219
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_219])])).

fof(f7154,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_96 ),
    inference(forward_demodulation,[],[f156,f1120])).

fof(f1120,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f1118])).

fof(f7153,plain,
    ( ~ spl6_219
    | spl6_15
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f7152,f991,f222,f3223])).

fof(f222,plain,
    ( spl6_15
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f7152,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_15
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f223,f993])).

fof(f223,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f222])).

fof(f7142,plain,
    ( spl6_220
    | ~ spl6_44
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f7141,f991,f521,f3231])).

fof(f3231,plain,
    ( spl6_220
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_220])])).

fof(f521,plain,
    ( spl6_44
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f7141,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_44
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f522,f993])).

fof(f522,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f521])).

fof(f7140,plain,
    ( ~ spl6_152
    | spl6_46
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f7139,f991,f529,f1947])).

fof(f1947,plain,
    ( spl6_152
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_152])])).

fof(f529,plain,
    ( spl6_46
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f7139,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl6_46
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f530,f993])).

fof(f530,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl6_46 ),
    inference(avatar_component_clause,[],[f529])).

fof(f7123,plain,
    ( ~ spl6_100
    | ~ spl6_96
    | spl6_101 ),
    inference(avatar_split_clause,[],[f7122,f1149,f1118,f1143])).

fof(f1143,plain,
    ( spl6_100
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f1149,plain,
    ( spl6_101
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f7122,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_96
    | spl6_101 ),
    inference(forward_demodulation,[],[f1150,f1120])).

fof(f1150,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_101 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f7093,plain,
    ( spl6_100
    | ~ spl6_111
    | ~ spl6_112
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_78
    | ~ spl6_79
    | ~ spl6_93
    | ~ spl6_104 ),
    inference(avatar_split_clause,[],[f7092,f1178,f1088,f912,f907,f210,f205,f1297,f1293,f1143])).

fof(f1297,plain,
    ( spl6_112
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f907,plain,
    ( spl6_78
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f912,plain,
    ( spl6_79
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f1088,plain,
    ( spl6_93
  <=> ! [X1,X2] :
        ( ~ v5_pre_topc(k1_xboole_0,X1,X2)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f7092,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_78
    | ~ spl6_79
    | ~ spl6_93
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f7091,f913])).

fof(f913,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f912])).

fof(f7091,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_78
    | ~ spl6_93
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f7090,f909])).

fof(f909,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f907])).

fof(f7090,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_93
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f7089,f207])).

fof(f7089,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_13
    | ~ spl6_93
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f5856,f212])).

fof(f5856,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_93
    | ~ spl6_104 ),
    inference(resolution,[],[f1180,f1089])).

fof(f1089,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v5_pre_topc(k1_xboole_0,X1,X2)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) )
    | ~ spl6_93 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f7084,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != u1_struct_0(sK1)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f7080,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6915,plain,
    ( sK2 != sK3
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6904,plain,
    ( ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_92
    | spl6_95
    | ~ spl6_97
    | ~ spl6_152
    | ~ spl6_322 ),
    inference(avatar_contradiction_clause,[],[f6903])).

fof(f6903,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_92
    | spl6_95
    | ~ spl6_97
    | ~ spl6_152
    | ~ spl6_322 ),
    inference(subsumption_resolution,[],[f6902,f1114])).

fof(f1114,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl6_95 ),
    inference(avatar_component_clause,[],[f1113])).

fof(f6902,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_92
    | ~ spl6_97
    | ~ spl6_152
    | ~ spl6_322 ),
    inference(subsumption_resolution,[],[f6901,f1948])).

fof(f1948,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_152 ),
    inference(avatar_component_clause,[],[f1947])).

fof(f6901,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_92
    | ~ spl6_97
    | ~ spl6_322 ),
    inference(subsumption_resolution,[],[f6900,f1127])).

fof(f6900,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_92
    | ~ spl6_322 ),
    inference(subsumption_resolution,[],[f6899,f207])).

fof(f6899,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_92
    | ~ spl6_322 ),
    inference(subsumption_resolution,[],[f6890,f212])).

fof(f6890,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_92
    | ~ spl6_322 ),
    inference(resolution,[],[f5832,f6064])).

fof(f6064,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_322 ),
    inference(avatar_component_clause,[],[f6062])).

fof(f5832,plain,
    ( ! [X45] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45))),k1_xboole_0)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X45),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)),sK1)
        | v5_pre_topc(k1_xboole_0,X45,sK1) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_92 ),
    inference(subsumption_resolution,[],[f5831,f197])).

fof(f5831,plain,
    ( ! [X45] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45))),k1_xboole_0)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X45),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)),sK1)
        | v5_pre_topc(k1_xboole_0,X45,sK1) )
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_92 ),
    inference(subsumption_resolution,[],[f5676,f202])).

fof(f5676,plain,
    ( ! [X45] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45))),k1_xboole_0)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X45),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)),sK1)
        | v5_pre_topc(k1_xboole_0,X45,sK1) )
    | ~ spl6_38
    | ~ spl6_92 ),
    inference(superposition,[],[f1084,f476])).

fof(f1084,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
        | v5_pre_topc(k1_xboole_0,X1,X2) )
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1083,plain,
    ( spl6_92
  <=> ! [X1,X2] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
        | v5_pre_topc(k1_xboole_0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f6435,plain,
    ( ~ spl6_31
    | ~ spl6_77
    | ~ spl6_85
    | spl6_230 ),
    inference(avatar_contradiction_clause,[],[f6431])).

fof(f6431,plain,
    ( $false
    | ~ spl6_31
    | ~ spl6_77
    | ~ spl6_85
    | spl6_230 ),
    inference(unit_resulting_resolution,[],[f903,f3361,f2752])).

fof(f2752,plain,
    ( ! [X2] :
        ( k1_xboole_0 = X2
        | ~ v1_xboole_0(X2) )
    | ~ spl6_31
    | ~ spl6_85 ),
    inference(resolution,[],[f1698,f1555])).

fof(f1555,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl6_31
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f1554,f993])).

fof(f1554,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK2) )
    | ~ spl6_31
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f998,f993])).

fof(f998,plain,
    ( ! [X0] :
        ( sK2 = X0
        | ~ r1_tarski(X0,sK2) )
    | ~ spl6_31 ),
    inference(resolution,[],[f995,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f995,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl6_31 ),
    inference(resolution,[],[f390,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f390,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl6_31
  <=> ! [X7] : ~ r2_hidden(X7,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f1698,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f287,f123])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f285,f129])).

fof(f129,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f285,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v1_xboole_0(k1_tarski(X0))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f130,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f130,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f3361,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_230 ),
    inference(avatar_component_clause,[],[f3360])).

fof(f903,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f902])).

fof(f6065,plain,
    ( spl6_322
    | ~ spl6_38
    | ~ spl6_220 ),
    inference(avatar_split_clause,[],[f6060,f3231,f474,f6062])).

fof(f6060,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_38
    | ~ spl6_220 ),
    inference(forward_demodulation,[],[f3232,f476])).

fof(f3232,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl6_220 ),
    inference(avatar_component_clause,[],[f3231])).

fof(f6058,plain,
    ( spl6_321
    | ~ spl6_23
    | ~ spl6_103
    | ~ spl6_110 ),
    inference(avatar_split_clause,[],[f6049,f1255,f1166,f281,f6055])).

fof(f281,plain,
    ( spl6_23
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f6049,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_23
    | ~ spl6_103
    | ~ spl6_110 ),
    inference(resolution,[],[f5949,f1257])).

fof(f1257,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_110 ),
    inference(avatar_component_clause,[],[f1255])).

fof(f5949,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(k1_xboole_0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_23
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f5948,f283])).

fof(f283,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f281])).

fof(f5948,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_partfun1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_103 ),
    inference(subsumption_resolution,[],[f5939,f314])).

fof(f314,plain,(
    ! [X1] : v4_relat_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f127,f118])).

fof(f5939,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_partfun1(k1_xboole_0,X0)
        | ~ v4_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_103 ),
    inference(superposition,[],[f1168,f107])).

fof(f5893,plain,
    ( ~ spl6_18
    | spl6_284 ),
    inference(avatar_contradiction_clause,[],[f5889])).

fof(f5889,plain,
    ( $false
    | ~ spl6_18
    | spl6_284 ),
    inference(unit_resulting_resolution,[],[f269,f1825,f125,f4764,f107])).

fof(f4764,plain,
    ( k1_xboole_0 != k1_relat_1(k6_partfun1(k1_xboole_0))
    | spl6_284 ),
    inference(avatar_component_clause,[],[f4763])).

fof(f4763,plain,
    ( spl6_284
  <=> k1_xboole_0 = k1_relat_1(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_284])])).

fof(f125,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f1825,plain,
    ( ! [X0] : v4_relat_1(k6_partfun1(k1_xboole_0),X0)
    | ~ spl6_18 ),
    inference(resolution,[],[f317,f243])).

fof(f243,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl6_18
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f317,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f127,f140])).

fof(f269,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(resolution,[],[f128,f126])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f5484,plain,
    ( spl6_103
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_31
    | ~ spl6_85
    | ~ spl6_284 ),
    inference(avatar_split_clause,[],[f5483,f4763,f991,f389,f241,f215,f1166])).

fof(f215,plain,
    ( spl6_14
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f5483,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_31
    | ~ spl6_85
    | ~ spl6_284 ),
    inference(subsumption_resolution,[],[f4787,f217])).

fof(f217,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f215])).

fof(f4787,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_31
    | ~ spl6_85
    | ~ spl6_284 ),
    inference(superposition,[],[f4765,f4532])).

fof(f4532,plain,
    ( ! [X4] :
        ( k1_xboole_0 = k6_partfun1(X4)
        | ~ v1_xboole_0(X4) )
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_31
    | ~ spl6_85 ),
    inference(resolution,[],[f4301,f1555])).

fof(f4301,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k6_partfun1(X0),X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_31
    | ~ spl6_85 ),
    inference(resolution,[],[f2780,f123])).

fof(f2780,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k6_partfun1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_31
    | ~ spl6_85 ),
    inference(superposition,[],[f600,f2752])).

fof(f600,plain,
    ( ! [X0] : ~ r2_hidden(X0,k6_partfun1(k1_xboole_0))
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f597,f217])).

fof(f597,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X0,k6_partfun1(k1_xboole_0)) )
    | ~ spl6_18 ),
    inference(resolution,[],[f243,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f4765,plain,
    ( k1_xboole_0 = k1_relat_1(k6_partfun1(k1_xboole_0))
    | ~ spl6_284 ),
    inference(avatar_component_clause,[],[f4763])).

fof(f5451,plain,
    ( spl6_104
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f5450,f991,f897,f1178])).

fof(f897,plain,
    ( spl6_76
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f5450,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_76
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f899,f993])).

fof(f899,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f897])).

fof(f5444,plain,
    ( spl6_152
    | ~ spl6_46
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f5443,f991,f529,f1947])).

fof(f5443,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_46
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f531,f993])).

fof(f531,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f529])).

fof(f5442,plain,
    ( spl6_219
    | ~ spl6_15
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f5441,f991,f222,f3223])).

fof(f5441,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_15
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f224,f993])).

fof(f224,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f222])).

fof(f5440,plain,
    ( spl6_219
    | ~ spl6_2
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f5439,f1118,f154,f3223])).

fof(f5439,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_96 ),
    inference(forward_demodulation,[],[f155,f1120])).

fof(f5432,plain,
    ( ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92
    | spl6_95
    | ~ spl6_194
    | ~ spl6_217
    | ~ spl6_257 ),
    inference(avatar_contradiction_clause,[],[f5431])).

fof(f5431,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92
    | spl6_95
    | ~ spl6_194
    | ~ spl6_217
    | ~ spl6_257 ),
    inference(subsumption_resolution,[],[f5430,f1114])).

fof(f5430,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92
    | ~ spl6_194
    | ~ spl6_217
    | ~ spl6_257 ),
    inference(subsumption_resolution,[],[f5429,f202])).

fof(f5429,plain,
    ( ~ v2_pre_topc(sK1)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92
    | ~ spl6_194
    | ~ spl6_217
    | ~ spl6_257 ),
    inference(subsumption_resolution,[],[f5426,f197])).

fof(f5426,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92
    | ~ spl6_194
    | ~ spl6_217
    | ~ spl6_257 ),
    inference(resolution,[],[f2902,f5258])).

fof(f5258,plain,
    ( ! [X44] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44)
        | ~ l1_pre_topc(X44)
        | ~ v2_pre_topc(X44)
        | v5_pre_topc(k1_xboole_0,sK0,X44) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92
    | ~ spl6_217
    | ~ spl6_257 ),
    inference(subsumption_resolution,[],[f5257,f3098])).

fof(f3098,plain,
    ( ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4)
    | ~ spl6_217 ),
    inference(avatar_component_clause,[],[f3097])).

fof(f5257,plain,
    ( ! [X44] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X44))
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44)
        | v5_pre_topc(k1_xboole_0,sK0,X44) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92
    | ~ spl6_217
    | ~ spl6_257 ),
    inference(forward_demodulation,[],[f5256,f3881])).

fof(f3881,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl6_257 ),
    inference(avatar_component_clause,[],[f3880])).

fof(f3880,plain,
    ( spl6_257
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_257])])).

fof(f5256,plain,
    ( ! [X44] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X44))
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44)
        | v5_pre_topc(k1_xboole_0,sK0,X44) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92
    | ~ spl6_217 ),
    inference(subsumption_resolution,[],[f3686,f3098])).

fof(f3686,plain,
    ( ! [X44] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X44))
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X44))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44)
        | v5_pre_topc(k1_xboole_0,sK0,X44) )
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92 ),
    inference(subsumption_resolution,[],[f3685,f207])).

fof(f3685,plain,
    ( ! [X44] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X44))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X44))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44)
        | v5_pre_topc(k1_xboole_0,sK0,X44) )
    | ~ spl6_13
    | ~ spl6_84
    | ~ spl6_92 ),
    inference(subsumption_resolution,[],[f3551,f212])).

fof(f3551,plain,
    ( ! [X44] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X44))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X44))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44)
        | v5_pre_topc(k1_xboole_0,sK0,X44) )
    | ~ spl6_84
    | ~ spl6_92 ),
    inference(superposition,[],[f1084,f989])).

fof(f989,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f987])).

fof(f987,plain,
    ( spl6_84
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f2902,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl6_194 ),
    inference(avatar_component_clause,[],[f2901])).

fof(f2901,plain,
    ( spl6_194
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_194])])).

fof(f5401,plain,
    ( ~ spl6_95
    | spl6_1
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f5400,f991,f150,f1113])).

fof(f5400,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl6_1
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f152,f993])).

fof(f152,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f150])).

fof(f5399,plain,
    ( spl6_227
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f5398,f1118,f987,f154,f3319])).

fof(f3319,plain,
    ( spl6_227
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_227])])).

fof(f5398,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_84
    | ~ spl6_96 ),
    inference(forward_demodulation,[],[f5397,f1120])).

fof(f5397,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_84 ),
    inference(forward_demodulation,[],[f155,f989])).

fof(f5378,plain,
    ( spl6_194
    | ~ spl6_227
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_90
    | ~ spl6_94
    | ~ spl6_109
    | ~ spl6_217
    | ~ spl6_228
    | ~ spl6_257 ),
    inference(avatar_split_clause,[],[f5377,f3880,f3323,f3097,f1236,f1093,f1038,f200,f195,f3319,f2901])).

fof(f1038,plain,
    ( spl6_90
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f1093,plain,
    ( spl6_94
  <=> ! [X1,X2] :
        ( ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
        | v5_pre_topc(k1_xboole_0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f1236,plain,
    ( spl6_109
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f5377,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_90
    | ~ spl6_94
    | ~ spl6_109
    | ~ spl6_217
    | ~ spl6_228
    | ~ spl6_257 ),
    inference(subsumption_resolution,[],[f5376,f3098])).

fof(f5376,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_90
    | ~ spl6_94
    | ~ spl6_109
    | ~ spl6_228
    | ~ spl6_257 ),
    inference(forward_demodulation,[],[f5375,f3881])).

fof(f5375,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_90
    | ~ spl6_94
    | ~ spl6_109
    | ~ spl6_228 ),
    inference(subsumption_resolution,[],[f5374,f197])).

fof(f5374,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl6_11
    | ~ spl6_90
    | ~ spl6_94
    | ~ spl6_109
    | ~ spl6_228 ),
    inference(subsumption_resolution,[],[f5373,f202])).

fof(f5373,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl6_90
    | ~ spl6_94
    | ~ spl6_109
    | ~ spl6_228 ),
    inference(subsumption_resolution,[],[f5372,f1237])).

fof(f1237,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl6_109 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f5372,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl6_90
    | ~ spl6_94
    | ~ spl6_228 ),
    inference(subsumption_resolution,[],[f4809,f1040])).

fof(f1040,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f4809,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)
    | ~ spl6_94
    | ~ spl6_228 ),
    inference(resolution,[],[f3324,f1094])).

fof(f1094,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
        | ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
        | v5_pre_topc(k1_xboole_0,X1,X2) )
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f3324,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_228 ),
    inference(avatar_component_clause,[],[f3323])).

fof(f4859,plain,
    ( spl6_257
    | ~ spl6_103
    | ~ spl6_232 ),
    inference(avatar_split_clause,[],[f4858,f3393,f1166,f3880])).

fof(f4858,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl6_103
    | ~ spl6_232 ),
    inference(forward_demodulation,[],[f4857,f1168])).

fof(f4857,plain,
    ( k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl6_232 ),
    inference(subsumption_resolution,[],[f4852,f118])).

fof(f4852,plain,
    ( k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_232 ),
    inference(superposition,[],[f100,f3395])).

fof(f3395,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl6_232 ),
    inference(avatar_component_clause,[],[f3393])).

fof(f4614,plain,
    ( ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_84
    | ~ spl6_95
    | ~ spl6_217
    | spl6_223 ),
    inference(avatar_contradiction_clause,[],[f4613])).

fof(f4613,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_84
    | ~ spl6_95
    | ~ spl6_217
    | spl6_223 ),
    inference(subsumption_resolution,[],[f4612,f3098])).

fof(f4612,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_84
    | ~ spl6_95
    | ~ spl6_217
    | spl6_223 ),
    inference(forward_demodulation,[],[f4611,f989])).

fof(f4611,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_84
    | ~ spl6_95
    | ~ spl6_217
    | spl6_223 ),
    inference(subsumption_resolution,[],[f4610,f3098])).

fof(f4610,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_84
    | ~ spl6_95
    | spl6_223 ),
    inference(forward_demodulation,[],[f4609,f989])).

fof(f4609,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_95
    | spl6_223 ),
    inference(subsumption_resolution,[],[f4608,f1115])).

fof(f4608,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_41
    | spl6_223 ),
    inference(subsumption_resolution,[],[f4607,f207])).

fof(f4607,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_41
    | spl6_223 ),
    inference(subsumption_resolution,[],[f4605,f212])).

fof(f4605,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_40
    | ~ spl6_41
    | spl6_223 ),
    inference(resolution,[],[f3266,f4042])).

fof(f4042,plain,
    ( ! [X11] :
        ( v5_pre_topc(k1_xboole_0,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X11),u1_struct_0(sK1))
        | ~ v5_pre_topc(k1_xboole_0,X11,sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X11),k1_xboole_0) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_40
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f4041,f197])).

fof(f4041,plain,
    ( ! [X11] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X11),k1_xboole_0)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X11),u1_struct_0(sK1))
        | ~ v5_pre_topc(k1_xboole_0,X11,sK1)
        | v5_pre_topc(k1_xboole_0,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl6_11
    | ~ spl6_40
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f3958,f202])).

fof(f3958,plain,
    ( ! [X11] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X11),k1_xboole_0)
        | ~ v2_pre_topc(X11)
        | ~ l1_pre_topc(X11)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X11),u1_struct_0(sK1))
        | ~ v5_pre_topc(k1_xboole_0,X11,sK1)
        | v5_pre_topc(k1_xboole_0,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl6_40
    | ~ spl6_41 ),
    inference(superposition,[],[f500,f486])).

fof(f3266,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_223 ),
    inference(avatar_component_clause,[],[f3265])).

fof(f3265,plain,
    ( spl6_223
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_223])])).

fof(f4573,plain,
    ( ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_84
    | ~ spl6_94
    | spl6_95
    | ~ spl6_217
    | ~ spl6_223 ),
    inference(avatar_contradiction_clause,[],[f4572])).

fof(f4572,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_84
    | ~ spl6_94
    | spl6_95
    | ~ spl6_217
    | ~ spl6_223 ),
    inference(subsumption_resolution,[],[f4571,f3098])).

fof(f4571,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_84
    | ~ spl6_94
    | spl6_95
    | ~ spl6_217
    | ~ spl6_223 ),
    inference(forward_demodulation,[],[f4570,f989])).

fof(f4570,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_84
    | ~ spl6_94
    | spl6_95
    | ~ spl6_217
    | ~ spl6_223 ),
    inference(subsumption_resolution,[],[f4569,f3098])).

fof(f4569,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_84
    | ~ spl6_94
    | spl6_95
    | ~ spl6_223 ),
    inference(forward_demodulation,[],[f4568,f989])).

fof(f4568,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_94
    | spl6_95
    | ~ spl6_223 ),
    inference(subsumption_resolution,[],[f4567,f1114])).

fof(f4567,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_94
    | ~ spl6_223 ),
    inference(subsumption_resolution,[],[f4566,f207])).

fof(f4566,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_40
    | ~ spl6_94
    | ~ spl6_223 ),
    inference(subsumption_resolution,[],[f4559,f212])).

fof(f4559,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_40
    | ~ spl6_94
    | ~ spl6_223 ),
    inference(resolution,[],[f4083,f3267])).

fof(f3267,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_223 ),
    inference(avatar_component_clause,[],[f3265])).

fof(f4083,plain,
    ( ! [X23] :
        ( ~ v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(sK1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0)
        | v5_pre_topc(k1_xboole_0,X23,sK1) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_40
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f4082,f197])).

fof(f4082,plain,
    ( ! [X23] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(sK1))
        | ~ v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X23,sK1) )
    | ~ spl6_11
    | ~ spl6_40
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f3967,f202])).

fof(f3967,plain,
    ( ! [X23] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(sK1))
        | ~ v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X23,sK1) )
    | ~ spl6_40
    | ~ spl6_94 ),
    inference(superposition,[],[f1094,f486])).

fof(f4337,plain,
    ( ~ spl6_103
    | spl6_136
    | ~ spl6_217 ),
    inference(avatar_contradiction_clause,[],[f4336])).

fof(f4336,plain,
    ( $false
    | ~ spl6_103
    | spl6_136
    | ~ spl6_217 ),
    inference(subsumption_resolution,[],[f4335,f3098])).

fof(f4335,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_103
    | spl6_136 ),
    inference(forward_demodulation,[],[f1759,f1168])).

fof(f1759,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl6_136 ),
    inference(avatar_component_clause,[],[f1758])).

fof(f1758,plain,
    ( spl6_136
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).

fof(f3764,plain,
    ( ~ spl6_84
    | ~ spl6_217
    | spl6_225 ),
    inference(avatar_contradiction_clause,[],[f3763])).

fof(f3763,plain,
    ( $false
    | ~ spl6_84
    | ~ spl6_217
    | spl6_225 ),
    inference(subsumption_resolution,[],[f3762,f3098])).

fof(f3762,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_84
    | spl6_225 ),
    inference(forward_demodulation,[],[f3275,f989])).

fof(f3275,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl6_225 ),
    inference(avatar_component_clause,[],[f3273])).

fof(f3273,plain,
    ( spl6_225
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_225])])).

fof(f3761,plain,
    ( ~ spl6_10
    | spl6_48 ),
    inference(avatar_contradiction_clause,[],[f3760])).

fof(f3760,plain,
    ( $false
    | ~ spl6_10
    | spl6_48 ),
    inference(subsumption_resolution,[],[f3758,f197])).

fof(f3758,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_48 ),
    inference(resolution,[],[f563,f292])).

fof(f563,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_48 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl6_48
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f3563,plain,
    ( spl6_91
    | ~ spl6_12
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f3562,f987,f205,f1044])).

fof(f1044,plain,
    ( spl6_91
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f3562,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_12
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f3520,f207])).

fof(f3520,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_84 ),
    inference(superposition,[],[f111,f989])).

fof(f3468,plain,
    ( spl6_84
    | ~ spl6_52
    | ~ spl6_85
    | ~ spl6_103 ),
    inference(avatar_split_clause,[],[f3414,f1166,f991,f590,f987])).

fof(f3414,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl6_52
    | ~ spl6_85
    | ~ spl6_103 ),
    inference(forward_demodulation,[],[f3413,f1168])).

fof(f3413,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl6_52
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f592,f993])).

fof(f3420,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | u1_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3399,plain,
    ( spl6_70
    | ~ spl6_85 ),
    inference(avatar_contradiction_clause,[],[f3398])).

fof(f3398,plain,
    ( $false
    | spl6_70
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f3397,f118])).

fof(f3397,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl6_70
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f745,f993])).

fof(f745,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl6_70 ),
    inference(avatar_component_clause,[],[f743])).

fof(f3290,plain,
    ( spl6_224
    | ~ spl6_16
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f3289,f991,f228,f3269])).

fof(f3269,plain,
    ( spl6_224
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_224])])).

fof(f3289,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_16
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f230,f993])).

fof(f3285,plain,
    ( ~ spl6_47
    | ~ spl6_48
    | ~ spl6_223
    | spl6_219
    | ~ spl6_224
    | ~ spl6_225
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f3284,f991,f453,f234,f210,f205,f3273,f3269,f3223,f3265,f561,f557])).

fof(f557,plain,
    ( spl6_47
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f453,plain,
    ( spl6_35
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f3284,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3283,f993])).

fof(f3283,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f3282,f118])).

fof(f3282,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3281,f993])).

fof(f3281,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f3280,f454])).

fof(f454,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f453])).

fof(f3280,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3279,f993])).

fof(f3279,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3278,f993])).

fof(f3278,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3277,f993])).

fof(f3277,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f1268,f993])).

fof(f1268,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f1267,f212])).

fof(f1267,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_12
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f534,f207])).

fof(f534,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_17 ),
    inference(resolution,[],[f147,f236])).

fof(f3276,plain,
    ( ~ spl6_47
    | ~ spl6_48
    | ~ spl6_219
    | spl6_223
    | ~ spl6_224
    | ~ spl6_225
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f3263,f991,f453,f234,f210,f205,f3273,f3269,f3265,f3223,f561,f557])).

fof(f3263,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3262,f993])).

fof(f3262,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f3261,f118])).

fof(f3261,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3260,f993])).

fof(f3260,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_35
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f3259,f454])).

fof(f3259,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3258,f993])).

fof(f3258,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3257,f993])).

fof(f3257,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3256,f993])).

fof(f3256,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f1274,f993])).

fof(f1274,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f1273,f212])).

fof(f1273,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_12
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f546,f207])).

fof(f546,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_17 ),
    inference(resolution,[],[f148,f236])).

fof(f3197,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ v1_partfun1(sK2,k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3189,plain,
    ( ~ spl6_103
    | spl6_106 ),
    inference(avatar_contradiction_clause,[],[f3181])).

fof(f3181,plain,
    ( $false
    | ~ spl6_103
    | spl6_106 ),
    inference(unit_resulting_resolution,[],[f1195,f118,f1168,f418])).

fof(f1195,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_106 ),
    inference(avatar_component_clause,[],[f1193])).

fof(f1193,plain,
    ( spl6_106
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f3152,plain,
    ( spl6_100
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f3151,f991,f474,f222,f1143])).

fof(f3151,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f3150,f993])).

fof(f3150,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_15
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f224,f476])).

fof(f3146,plain,
    ( ~ spl6_98
    | ~ spl6_38
    | spl6_44
    | ~ spl6_85
    | ~ spl6_133 ),
    inference(avatar_split_clause,[],[f3145,f1718,f991,f521,f474,f1130])).

fof(f1130,plain,
    ( spl6_98
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f3145,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_38
    | spl6_44
    | ~ spl6_85
    | ~ spl6_133 ),
    inference(forward_demodulation,[],[f3144,f993])).

fof(f3144,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_38
    | spl6_44
    | ~ spl6_133 ),
    inference(forward_demodulation,[],[f3143,f1720])).

fof(f1720,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl6_133 ),
    inference(avatar_component_clause,[],[f1718])).

fof(f3143,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_38
    | spl6_44 ),
    inference(forward_demodulation,[],[f523,f476])).

fof(f523,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl6_44 ),
    inference(avatar_component_clause,[],[f521])).

fof(f3127,plain,
    ( ~ spl6_100
    | ~ spl6_98
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_43
    | ~ spl6_94
    | ~ spl6_133
    | ~ spl6_136
    | spl6_152 ),
    inference(avatar_split_clause,[],[f3126,f1947,f1758,f1718,f1093,f517,f513,f474,f200,f195,f1130,f1143])).

fof(f517,plain,
    ( spl6_43
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f3126,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_43
    | ~ spl6_94
    | ~ spl6_133
    | ~ spl6_136
    | spl6_152 ),
    inference(subsumption_resolution,[],[f3125,f1949])).

fof(f1949,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl6_152 ),
    inference(avatar_component_clause,[],[f1947])).

fof(f3125,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_43
    | ~ spl6_94
    | ~ spl6_133
    | ~ spl6_136 ),
    inference(subsumption_resolution,[],[f3124,f518])).

fof(f518,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f517])).

fof(f3124,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_94
    | ~ spl6_133
    | ~ spl6_136 ),
    inference(subsumption_resolution,[],[f3123,f514])).

fof(f3123,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_94
    | ~ spl6_133
    | ~ spl6_136 ),
    inference(subsumption_resolution,[],[f2996,f1760])).

fof(f1760,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_136 ),
    inference(avatar_component_clause,[],[f1758])).

fof(f2996,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_94
    | ~ spl6_133 ),
    inference(superposition,[],[f2274,f1720])).

fof(f2274,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f2273,f197])).

fof(f2273,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f2263,f202])).

% (24938)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
fof(f2263,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | v5_pre_topc(k1_xboole_0,X0,sK1) )
    | ~ spl6_38
    | ~ spl6_94 ),
    inference(superposition,[],[f1094,f476])).

fof(f3122,plain,
    ( ~ spl6_95
    | ~ spl6_98
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_93
    | ~ spl6_97
    | ~ spl6_133
    | spl6_152 ),
    inference(avatar_split_clause,[],[f3121,f1947,f1718,f1125,f1088,f474,f210,f205,f200,f195,f1130,f1113])).

fof(f3121,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_93
    | ~ spl6_97
    | ~ spl6_133
    | spl6_152 ),
    inference(subsumption_resolution,[],[f3089,f1949])).

fof(f3089,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_93
    | ~ spl6_97
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f3088,f1127])).

fof(f3088,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_93
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f3087,f207])).

fof(f3087,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_38
    | ~ spl6_93
    | ~ spl6_133 ),
    inference(subsumption_resolution,[],[f3069,f212])).

fof(f3069,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_93
    | ~ spl6_133 ),
    inference(superposition,[],[f2255,f1720])).

fof(f2255,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_93 ),
    inference(subsumption_resolution,[],[f2254,f197])).

fof(f2254,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) )
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_93 ),
    inference(subsumption_resolution,[],[f2241,f202])).

fof(f2241,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0)
        | ~ v5_pre_topc(k1_xboole_0,X0,sK1)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1) )
    | ~ spl6_38
    | ~ spl6_93 ),
    inference(superposition,[],[f1089,f476])).

fof(f1944,plain,
    ( ~ spl6_38
    | spl6_45
    | ~ spl6_85 ),
    inference(avatar_contradiction_clause,[],[f1943])).

fof(f1943,plain,
    ( $false
    | ~ spl6_38
    | spl6_45
    | ~ spl6_85 ),
    inference(subsumption_resolution,[],[f1942,f118])).

fof(f1942,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_38
    | spl6_45
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f1941,f993])).

fof(f1941,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_38
    | spl6_45 ),
    inference(forward_demodulation,[],[f1940,f140])).

fof(f1940,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl6_38
    | spl6_45 ),
    inference(forward_demodulation,[],[f527,f476])).

fof(f527,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl6_45 ),
    inference(avatar_component_clause,[],[f525])).

fof(f525,plain,
    ( spl6_45
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f1881,plain,
    ( ~ spl6_12
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f1880])).

fof(f1880,plain,
    ( $false
    | ~ spl6_12
    | spl6_43 ),
    inference(subsumption_resolution,[],[f1875,f207])).

fof(f1875,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_43 ),
    inference(resolution,[],[f292,f519])).

fof(f519,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f517])).

fof(f1723,plain,
    ( spl6_133
    | ~ spl6_132 ),
    inference(avatar_split_clause,[],[f1722,f1703,f1718])).

fof(f1703,plain,
    ( spl6_132
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).

fof(f1722,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl6_132 ),
    inference(subsumption_resolution,[],[f1714,f118])).

fof(f1714,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl6_132 ),
    inference(superposition,[],[f100,f1705])).

fof(f1705,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl6_132 ),
    inference(avatar_component_clause,[],[f1703])).

fof(f1706,plain,
    ( spl6_132
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f1701,f991,f480,f474,f1703])).

fof(f480,plain,
    ( spl6_39
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f1701,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f1700,f476])).

fof(f1700,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl6_39
    | ~ spl6_85 ),
    inference(forward_demodulation,[],[f482,f993])).

fof(f482,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f480])).

fof(f1549,plain,
    ( spl6_109
    | ~ spl6_91 ),
    inference(avatar_split_clause,[],[f1542,f1044,f1236])).

fof(f1542,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl6_91 ),
    inference(resolution,[],[f1046,f109])).

fof(f1046,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f1044])).

fof(f1408,plain,
    ( spl6_97
    | ~ spl6_74
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f1401,f991,f887,f1125])).

fof(f887,plain,
    ( spl6_74
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f1401,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_74
    | ~ spl6_85 ),
    inference(backward_demodulation,[],[f889,f993])).

fof(f889,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f887])).

fof(f1407,plain,
    ( spl6_35
    | ~ spl6_9
    | ~ spl6_85 ),
    inference(avatar_split_clause,[],[f1396,f991,f190,f453])).

fof(f1396,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_9
    | ~ spl6_85 ),
    inference(backward_demodulation,[],[f192,f993])).

fof(f1389,plain,
    ( ~ spl6_24
    | ~ spl6_31
    | spl6_85 ),
    inference(avatar_contradiction_clause,[],[f1386])).

fof(f1386,plain,
    ( $false
    | ~ spl6_24
    | ~ spl6_31
    | spl6_85 ),
    inference(unit_resulting_resolution,[],[f308,f992,f995,f106])).

fof(f992,plain,
    ( k1_xboole_0 != sK2
    | spl6_85 ),
    inference(avatar_component_clause,[],[f991])).

fof(f308,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_24 ),
    inference(resolution,[],[f303,f123])).

fof(f303,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl6_24
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f1375,plain,
    ( spl6_31
    | ~ spl6_14
    | ~ spl6_73 ),
    inference(avatar_split_clause,[],[f1374,f882,f215,f389])).

fof(f1374,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl6_14
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f1371,f217])).

fof(f1371,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_73 ),
    inference(resolution,[],[f884,f112])).

fof(f884,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f882])).

fof(f1370,plain,
    ( spl6_79
    | ~ spl6_38
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f1306,f561,f474,f912])).

fof(f1306,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_38
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f562,f476])).

fof(f562,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f561])).

fof(f1356,plain,
    ( ~ spl6_101
    | spl6_2
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1355,f474,f154,f1149])).

fof(f1355,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_2
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f156,f476])).

fof(f1342,plain,
    ( spl6_31
    | ~ spl6_7
    | ~ spl6_14
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1228,f474,f215,f180,f389])).

fof(f1228,plain,
    ( ! [X7] : ~ r2_hidden(X7,sK2)
    | ~ spl6_7
    | ~ spl6_14
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f1227,f217])).

fof(f1227,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X7,sK2) )
    | ~ spl6_7
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1226,f140])).

fof(f1226,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))
        | ~ r2_hidden(X7,sK2) )
    | ~ spl6_7
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f297,f476])).

fof(f297,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
        | ~ r2_hidden(X7,sK2) )
    | ~ spl6_7 ),
    inference(resolution,[],[f112,f182])).

fof(f1308,plain,
    ( sK2 != sK3
    | k1_xboole_0 != sK3
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1196,plain,
    ( ~ spl6_106
    | spl6_98
    | ~ spl6_103 ),
    inference(avatar_split_clause,[],[f1183,f1166,f1130,f1193])).

fof(f1183,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_98
    | ~ spl6_103 ),
    inference(backward_demodulation,[],[f1132,f1168])).

fof(f1132,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl6_98 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f1095,plain,
    ( ~ spl6_35
    | spl6_94 ),
    inference(avatar_split_clause,[],[f1091,f1093,f453])).

fof(f1091,plain,(
    ! [X2,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | v5_pre_topc(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f504,f118])).

fof(f504,plain,(
    ! [X2,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | v5_pre_topc(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f146,f118])).

fof(f1090,plain,
    ( ~ spl6_35
    | spl6_93 ),
    inference(avatar_split_clause,[],[f1086,f1088,f453])).

fof(f1086,plain,(
    ! [X2,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X1,X2)
      | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f536,f118])).

fof(f536,plain,(
    ! [X2,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X1,X2)
      | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f147,f118])).

fof(f1085,plain,
    ( ~ spl6_35
    | spl6_92 ),
    inference(avatar_split_clause,[],[f1081,f1083,f453])).

fof(f1081,plain,(
    ! [X2,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
      | v5_pre_topc(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f548,f118])).

fof(f548,plain,(
    ! [X2,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
      | v5_pre_topc(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f148,f118])).

fof(f1041,plain,
    ( spl6_90
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f1036,f987,f210,f205,f1038])).

fof(f1036,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f1035,f212])).

fof(f1035,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_12
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f1005,f207])).

fof(f1005,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl6_84 ),
    inference(superposition,[],[f110,f989])).

fof(f110,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f910,plain,
    ( spl6_78
    | ~ spl6_38
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f863,f557,f474,f907])).

fof(f863,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_38
    | ~ spl6_47 ),
    inference(backward_demodulation,[],[f558,f476])).

fof(f558,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f557])).

fof(f900,plain,
    ( spl6_76
    | ~ spl6_16
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f861,f474,f228,f897])).

fof(f861,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_16
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f230,f476])).

fof(f890,plain,
    ( spl6_74
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f859,f474,f185,f887])).

fof(f859,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f187,f476])).

fof(f835,plain,
    ( ~ spl6_42
    | ~ spl6_43
    | ~ spl6_44
    | ~ spl6_45
    | ~ spl6_16
    | spl6_46
    | ~ spl6_15
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f730,f234,f200,f195,f190,f222,f529,f228,f525,f521,f517,f513])).

fof(f730,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f729,f202])).

fof(f729,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f728,f197])).

fof(f728,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f502,f192])).

fof(f502,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_17 ),
    inference(resolution,[],[f146,f236])).

fof(f834,plain,
    ( ~ spl6_42
    | ~ spl6_43
    | ~ spl6_44
    | ~ spl6_45
    | ~ spl6_16
    | spl6_15
    | ~ spl6_46
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f753,f234,f200,f195,f190,f529,f222,f228,f525,f521,f517,f513])).

fof(f753,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f752,f202])).

fof(f752,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f751,f197])).

fof(f751,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_9
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f491,f192])).

fof(f491,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_17 ),
    inference(resolution,[],[f145,f236])).

fof(f672,plain,
    ( spl6_61
    | ~ spl6_26
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f614,f590,f320,f669])).

fof(f614,plain,
    ( v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl6_26
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f322,f592])).

fof(f322,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f320])).

fof(f642,plain,
    ( spl6_55
    | ~ spl6_8
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f608,f590,f185,f639])).

fof(f608,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl6_8
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f187,f592])).

fof(f637,plain,
    ( spl6_54
    | ~ spl6_7
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f607,f590,f180,f634])).

fof(f607,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl6_7
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f182,f592])).

fof(f595,plain,
    ( spl6_52
    | ~ spl6_7
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f594,f470,f180,f590])).

fof(f594,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_7
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f586,f182])).

fof(f586,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_37 ),
    inference(superposition,[],[f100,f472])).

fof(f472,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f470])).

fof(f583,plain,
    ( ~ spl6_10
    | ~ spl6_11
    | spl6_47 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_11
    | spl6_47 ),
    inference(subsumption_resolution,[],[f581,f202])).

fof(f581,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl6_10
    | spl6_47 ),
    inference(subsumption_resolution,[],[f579,f197])).

fof(f579,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_47 ),
    inference(resolution,[],[f559,f110])).

fof(f559,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_47 ),
    inference(avatar_component_clause,[],[f557])).

fof(f545,plain,
    ( ~ spl6_12
    | ~ spl6_13
    | spl6_42 ),
    inference(avatar_contradiction_clause,[],[f544])).

fof(f544,plain,
    ( $false
    | ~ spl6_12
    | ~ spl6_13
    | spl6_42 ),
    inference(subsumption_resolution,[],[f543,f212])).

fof(f543,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl6_12
    | spl6_42 ),
    inference(subsumption_resolution,[],[f541,f207])).

fof(f541,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_42 ),
    inference(resolution,[],[f515,f110])).

fof(f515,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl6_42 ),
    inference(avatar_component_clause,[],[f513])).

fof(f501,plain,
    ( ~ spl6_35
    | spl6_41 ),
    inference(avatar_split_clause,[],[f497,f499,f453])).

fof(f497,plain,(
    ! [X2,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X1,X2)
      | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f493,f118])).

fof(f493,plain,(
    ! [X2,X1] :
      ( ~ v5_pre_topc(k1_xboole_0,X1,X2)
      | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(resolution,[],[f145,f118])).

fof(f487,plain,
    ( spl6_39
    | spl6_40
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f478,f234,f228,f484,f480])).

fof(f478,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f461,f230])).

fof(f461,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl6_17 ),
    inference(resolution,[],[f94,f236])).

fof(f459,plain,
    ( ~ spl6_35
    | spl6_36 ),
    inference(avatar_split_clause,[],[f431,f457,f453])).

fof(f431,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(k1_xboole_0,X1,X2)
      | ~ v1_funct_1(k1_xboole_0)
      | v1_partfun1(k1_xboole_0,X1)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f120,f118])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f368,plain,(
    ~ spl6_25 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl6_25 ),
    inference(resolution,[],[f306,f116])).

fof(f116,plain,(
    ! [X0] : v1_xboole_0(sK4(X0)) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(X0))
      & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f6,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f306,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl6_25
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f328,plain,
    ( spl6_27
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f312,f234,f325])).

fof(f312,plain,
    ( v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl6_17 ),
    inference(resolution,[],[f127,f236])).

fof(f307,plain,
    ( spl6_24
    | spl6_25 ),
    inference(avatar_split_clause,[],[f294,f305,f302])).

fof(f294,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f112,f118])).

fof(f284,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f270,f281])).

fof(f270,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f128,f118])).

fof(f278,plain,
    ( spl6_22
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f267,f180,f275])).

fof(f267,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f128,f182])).

fof(f245,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f239,f241])).

fof(f239,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f126,f141])).

fof(f237,plain,
    ( spl6_17
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f232,f165,f160,f234])).

fof(f165,plain,
    ( spl6_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f232,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f167,f162])).

fof(f167,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f165])).

fof(f231,plain,
    ( spl6_16
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f226,f170,f160,f228])).

fof(f170,plain,
    ( spl6_5
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f226,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f172,f162])).

fof(f172,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f170])).

fof(f225,plain,
    ( spl6_15
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f220,f160,f154,f222])).

fof(f220,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f155,f162])).

fof(f218,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f121,f215])).

fof(f121,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f213,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f77,f210])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f61,f60,f59,f58])).

fof(f58,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f208,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f78,f205])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f203,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f79,f200])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f198,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f80,f195])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f193,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f81,f190])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f188,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f82,f185])).

fof(f82,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f183,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f83,f180])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f173,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f85,f170])).

fof(f85,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f168,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f86,f165])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f62])).

fof(f163,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f87,f160])).

fof(f87,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f62])).

fof(f158,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f88,f154,f150])).

fof(f88,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f157,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f89,f154,f150])).

fof(f89,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.53  % (24650)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (24642)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (24663)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (24656)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (24648)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (24641)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (24665)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (24646)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (24638)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (24647)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.55  % (24640)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.56  % (24655)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.56  % (24650)Refutation not found, incomplete strategy% (24650)------------------------------
% 1.53/0.56  % (24650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (24650)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (24650)Memory used [KB]: 10874
% 1.53/0.56  % (24650)Time elapsed: 0.150 s
% 1.53/0.56  % (24650)------------------------------
% 1.53/0.56  % (24650)------------------------------
% 1.53/0.56  % (24667)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.56  % (24656)Refutation not found, incomplete strategy% (24656)------------------------------
% 1.53/0.56  % (24656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (24656)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (24656)Memory used [KB]: 10746
% 1.53/0.56  % (24656)Time elapsed: 0.115 s
% 1.53/0.56  % (24656)------------------------------
% 1.53/0.56  % (24656)------------------------------
% 1.53/0.56  % (24649)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.56  % (24651)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.56  % (24658)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.57  % (24662)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.57  % (24652)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.57  % (24668)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.69/0.57  % (24644)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.69/0.57  % (24657)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.69/0.58  % (24659)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.69/0.58  % (24648)Refutation not found, incomplete strategy% (24648)------------------------------
% 1.69/0.58  % (24648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (24648)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (24648)Memory used [KB]: 10874
% 1.69/0.58  % (24648)Time elapsed: 0.127 s
% 1.69/0.58  % (24648)------------------------------
% 1.69/0.58  % (24648)------------------------------
% 1.69/0.58  % (24645)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.69/0.58  % (24669)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.69/0.58  % (24653)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.69/0.58  % (24639)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.69/0.59  % (24649)Refutation not found, incomplete strategy% (24649)------------------------------
% 1.69/0.59  % (24649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (24664)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.69/0.59  % (24649)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (24649)Memory used [KB]: 10874
% 1.69/0.59  % (24649)Time elapsed: 0.154 s
% 1.69/0.59  % (24649)------------------------------
% 1.69/0.59  % (24649)------------------------------
% 1.69/0.60  % (24654)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.69/0.60  % (24660)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.69/0.60  % (24661)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.69/0.60  % (24638)Refutation not found, incomplete strategy% (24638)------------------------------
% 1.69/0.60  % (24638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.60  % (24638)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.60  
% 1.69/0.60  % (24638)Memory used [KB]: 2046
% 1.69/0.60  % (24638)Time elapsed: 0.199 s
% 1.69/0.60  % (24638)------------------------------
% 1.69/0.60  % (24638)------------------------------
% 2.23/0.70  % (24687)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.23/0.71  % (24690)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.23/0.72  % (24688)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.71/0.74  % (24689)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.94/0.79  % (24691)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.94/0.84  % (24644)Time limit reached!
% 2.94/0.84  % (24644)------------------------------
% 2.94/0.84  % (24644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.94/0.84  % (24644)Termination reason: Time limit
% 2.94/0.84  
% 2.94/0.84  % (24644)Memory used [KB]: 7419
% 2.94/0.84  % (24644)Time elapsed: 0.418 s
% 2.94/0.84  % (24644)------------------------------
% 2.94/0.84  % (24644)------------------------------
% 3.46/0.86  % (24659)Refutation not found, incomplete strategy% (24659)------------------------------
% 3.46/0.86  % (24659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.46/0.86  % (24688)Refutation not found, incomplete strategy% (24688)------------------------------
% 3.46/0.86  % (24688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.46/0.86  % (24688)Termination reason: Refutation not found, incomplete strategy
% 3.46/0.86  
% 3.46/0.86  % (24688)Memory used [KB]: 6268
% 3.46/0.86  % (24688)Time elapsed: 0.257 s
% 3.46/0.86  % (24688)------------------------------
% 3.46/0.86  % (24688)------------------------------
% 3.46/0.86  % (24659)Termination reason: Refutation not found, incomplete strategy
% 3.46/0.86  
% 3.46/0.86  % (24659)Memory used [KB]: 12665
% 3.46/0.86  % (24659)Time elapsed: 0.461 s
% 3.46/0.86  % (24659)------------------------------
% 3.46/0.86  % (24659)------------------------------
% 3.73/0.90  % (24660)Refutation not found, incomplete strategy% (24660)------------------------------
% 3.73/0.90  % (24660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.90  % (24660)Termination reason: Refutation not found, incomplete strategy
% 3.73/0.90  
% 3.73/0.90  % (24660)Memory used [KB]: 2558
% 3.73/0.90  % (24660)Time elapsed: 0.484 s
% 3.73/0.90  % (24660)------------------------------
% 3.73/0.90  % (24660)------------------------------
% 3.73/0.92  % (24639)Time limit reached!
% 3.73/0.92  % (24639)------------------------------
% 3.73/0.92  % (24639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.73/0.92  % (24639)Termination reason: Time limit
% 3.73/0.92  % (24639)Termination phase: Saturation
% 3.73/0.92  
% 3.73/0.92  % (24639)Memory used [KB]: 6908
% 3.73/0.92  % (24639)Time elapsed: 0.500 s
% 3.73/0.92  % (24639)------------------------------
% 3.73/0.92  % (24639)------------------------------
% 4.09/0.94  % (24651)Time limit reached!
% 4.09/0.94  % (24651)------------------------------
% 4.09/0.94  % (24651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.94  % (24651)Termination reason: Time limit
% 4.09/0.94  
% 4.09/0.94  % (24651)Memory used [KB]: 8187
% 4.09/0.94  % (24651)Time elapsed: 0.515 s
% 4.09/0.94  % (24651)------------------------------
% 4.09/0.94  % (24651)------------------------------
% 4.26/0.97  % (24694)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.26/0.99  % (24695)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.26/1.00  % (24696)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.26/1.02  % (24701)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.64/1.03  % (24646)Time limit reached!
% 4.64/1.03  % (24646)------------------------------
% 4.64/1.03  % (24646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.03  % (24697)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.64/1.04  % (24655)Time limit reached!
% 4.64/1.04  % (24655)------------------------------
% 4.64/1.04  % (24655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.04  % (24646)Termination reason: Time limit
% 4.64/1.04  
% 4.64/1.04  % (24646)Memory used [KB]: 8443
% 4.64/1.04  % (24646)Time elapsed: 0.606 s
% 4.64/1.04  % (24646)------------------------------
% 4.64/1.04  % (24646)------------------------------
% 4.64/1.04  % (24655)Termination reason: Time limit
% 4.64/1.04  % (24655)Termination phase: Saturation
% 4.64/1.04  
% 4.64/1.04  % (24655)Memory used [KB]: 15223
% 4.64/1.04  % (24655)Time elapsed: 0.600 s
% 4.64/1.04  % (24655)------------------------------
% 4.64/1.04  % (24655)------------------------------
% 4.64/1.04  % (24712)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.64/1.05  % (24668)Time limit reached!
% 4.64/1.05  % (24668)------------------------------
% 4.64/1.05  % (24668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.05  % (24668)Termination reason: Time limit
% 4.64/1.05  
% 4.64/1.05  % (24668)Memory used [KB]: 7291
% 4.64/1.05  % (24668)Time elapsed: 0.625 s
% 4.64/1.05  % (24668)------------------------------
% 4.64/1.05  % (24668)------------------------------
% 4.64/1.05  % (24691)Time limit reached!
% 4.64/1.05  % (24691)------------------------------
% 4.64/1.05  % (24691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.05  % (24691)Termination reason: Time limit
% 4.64/1.05  
% 4.64/1.05  % (24691)Memory used [KB]: 12409
% 4.64/1.05  % (24691)Time elapsed: 0.416 s
% 4.64/1.05  % (24691)------------------------------
% 4.64/1.05  % (24691)------------------------------
% 5.65/1.11  % (24690)Time limit reached!
% 5.65/1.11  % (24690)------------------------------
% 5.65/1.11  % (24690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.65/1.12  % (24690)Termination reason: Time limit
% 5.65/1.12  
% 5.65/1.12  % (24690)Memory used [KB]: 7036
% 5.65/1.12  % (24690)Time elapsed: 0.420 s
% 5.65/1.12  % (24690)------------------------------
% 5.65/1.12  % (24690)------------------------------
% 5.65/1.14  % (24760)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.24/1.18  % (24752)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.24/1.18  % (24757)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.47/1.19  % (24755)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.81/1.24  % (24802)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 8.56/1.45  % (24640)Time limit reached!
% 8.56/1.45  % (24640)------------------------------
% 8.56/1.45  % (24640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.56/1.46  % (24640)Termination reason: Time limit
% 8.56/1.46  
% 8.56/1.46  % (24640)Memory used [KB]: 13816
% 8.56/1.46  % (24640)Time elapsed: 1.025 s
% 8.56/1.46  % (24640)------------------------------
% 8.56/1.46  % (24640)------------------------------
% 9.21/1.56  % (24917)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 9.21/1.59  % (24755)Time limit reached!
% 9.21/1.59  % (24755)------------------------------
% 9.21/1.59  % (24755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.21/1.59  % (24755)Termination reason: Time limit
% 9.21/1.59  
% 9.21/1.59  % (24755)Memory used [KB]: 2302
% 9.21/1.59  % (24755)Time elapsed: 0.509 s
% 9.21/1.59  % (24755)------------------------------
% 9.21/1.59  % (24755)------------------------------
% 9.98/1.62  % (24665)Time limit reached!
% 9.98/1.62  % (24665)------------------------------
% 9.98/1.62  % (24665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.98/1.62  % (24665)Termination reason: Time limit
% 9.98/1.62  
% 9.98/1.62  % (24665)Memory used [KB]: 14200
% 9.98/1.62  % (24665)Time elapsed: 1.216 s
% 9.98/1.62  % (24665)------------------------------
% 9.98/1.62  % (24665)------------------------------
% 9.98/1.65  % (24661)Time limit reached!
% 9.98/1.65  % (24661)------------------------------
% 9.98/1.65  % (24661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.98/1.65  % (24661)Termination reason: Time limit
% 9.98/1.65  
% 9.98/1.65  % (24661)Memory used [KB]: 16247
% 9.98/1.65  % (24661)Time elapsed: 1.229 s
% 9.98/1.65  % (24661)------------------------------
% 9.98/1.65  % (24661)------------------------------
% 10.36/1.72  % (24933)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 10.36/1.73  % (24654)Time limit reached!
% 10.36/1.73  % (24654)------------------------------
% 10.36/1.73  % (24654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.36/1.73  % (24654)Termination reason: Time limit
% 10.36/1.73  
% 10.36/1.73  % (24654)Memory used [KB]: 23155
% 10.36/1.73  % (24654)Time elapsed: 1.314 s
% 10.36/1.73  % (24654)------------------------------
% 10.36/1.73  % (24654)------------------------------
% 10.36/1.74  % (24663)Time limit reached!
% 10.36/1.74  % (24663)------------------------------
% 10.36/1.74  % (24663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.36/1.74  % (24663)Termination reason: Time limit
% 10.36/1.74  
% 10.36/1.74  % (24663)Memory used [KB]: 22387
% 10.36/1.74  % (24663)Time elapsed: 1.305 s
% 10.36/1.74  % (24663)------------------------------
% 10.36/1.74  % (24663)------------------------------
% 10.36/1.75  % (24934)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 11.21/1.79  % (24935)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 11.58/1.89  % (24936)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 11.58/1.90  % (24937)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 12.08/1.91  % (24917)Time limit reached!
% 12.08/1.91  % (24917)------------------------------
% 12.08/1.91  % (24917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.91  % (24917)Termination reason: Time limit
% 12.08/1.91  
% 12.08/1.91  % (24917)Memory used [KB]: 4349
% 12.08/1.91  % (24917)Time elapsed: 0.405 s
% 12.08/1.91  % (24917)------------------------------
% 12.08/1.91  % (24917)------------------------------
% 12.08/1.93  % (24642)Time limit reached!
% 12.08/1.93  % (24642)------------------------------
% 12.08/1.93  % (24642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.93  % (24667)Time limit reached!
% 12.08/1.93  % (24667)------------------------------
% 12.08/1.93  % (24667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.08/1.94  % (24667)Termination reason: Time limit
% 12.08/1.94  % (24667)Termination phase: Saturation
% 12.08/1.94  
% 12.08/1.94  % (24667)Memory used [KB]: 14967
% 12.08/1.94  % (24667)Time elapsed: 1.500 s
% 12.08/1.94  % (24667)------------------------------
% 12.08/1.94  % (24667)------------------------------
% 12.08/1.94  % (24642)Termination reason: Time limit
% 12.08/1.94  
% 12.08/1.94  % (24642)Memory used [KB]: 14583
% 12.08/1.94  % (24642)Time elapsed: 1.527 s
% 12.08/1.94  % (24642)------------------------------
% 12.08/1.94  % (24642)------------------------------
% 12.55/1.98  % (24689)Refutation found. Thanks to Tanya!
% 12.55/1.98  % SZS status Theorem for theBenchmark
% 12.55/1.98  % SZS output start Proof for theBenchmark
% 12.55/1.98  fof(f13261,plain,(
% 12.55/1.98    $false),
% 12.55/1.98    inference(avatar_sat_refutation,[],[f157,f158,f163,f168,f173,f183,f188,f193,f198,f203,f208,f213,f218,f225,f231,f237,f245,f278,f284,f307,f328,f368,f459,f487,f501,f545,f583,f595,f637,f642,f672,f834,f835,f890,f900,f910,f1041,f1085,f1090,f1095,f1196,f1308,f1342,f1356,f1370,f1375,f1389,f1407,f1408,f1549,f1706,f1723,f1881,f1944,f3122,f3127,f3146,f3152,f3189,f3197,f3276,f3285,f3290,f3399,f3420,f3468,f3563,f3761,f3764,f4337,f4573,f4614,f4859,f5378,f5399,f5401,f5432,f5440,f5442,f5444,f5451,f5484,f5893,f6058,f6065,f6435,f6904,f6915,f7080,f7084,f7093,f7123,f7140,f7142,f7153,f7155,f7157,f7413,f7502,f7737,f7825,f7887,f7913,f7914,f7946,f7953,f8030,f8150,f8301,f8313,f8360,f8430,f8708,f9693,f9698,f9699,f9707,f9842,f10087,f10098,f10227,f10543,f12459,f12466,f13258])).
% 12.55/1.99  fof(f13258,plain,(
% 12.55/1.99    ~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55 | ~spl6_63 | spl6_69 | ~spl6_70 | ~spl6_413),
% 12.55/1.99    inference(avatar_contradiction_clause,[],[f13257])).
% 12.55/1.99  fof(f13257,plain,(
% 12.55/1.99    $false | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55 | ~spl6_63 | spl6_69 | ~spl6_70 | ~spl6_413)),
% 12.55/1.99    inference(subsumption_resolution,[],[f13256,f641])).
% 12.55/1.99  fof(f641,plain,(
% 12.55/1.99    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl6_55),
% 12.55/1.99    inference(avatar_component_clause,[],[f639])).
% 12.55/1.99  fof(f639,plain,(
% 12.55/1.99    spl6_55 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 12.55/1.99    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 12.55/1.99  fof(f13256,plain,(
% 12.55/1.99    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55 | ~spl6_63 | spl6_69 | ~spl6_70 | ~spl6_413)),
% 12.55/1.99    inference(forward_demodulation,[],[f13255,f592])).
% 12.55/1.99  fof(f592,plain,(
% 12.55/1.99    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl6_52),
% 12.55/1.99    inference(avatar_component_clause,[],[f590])).
% 12.55/1.99  fof(f590,plain,(
% 12.55/1.99    spl6_52 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 12.55/1.99    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 12.55/1.99  fof(f13255,plain,(
% 12.55/1.99    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55 | ~spl6_63 | spl6_69 | ~spl6_70 | ~spl6_413)),
% 12.55/1.99    inference(subsumption_resolution,[],[f13254,f636])).
% 12.55/1.99  fof(f636,plain,(
% 12.55/1.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl6_54),
% 12.55/1.99    inference(avatar_component_clause,[],[f634])).
% 12.55/1.99  fof(f634,plain,(
% 12.55/1.99    spl6_54 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 12.55/1.99    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 12.55/1.99  fof(f13254,plain,(
% 12.55/1.99    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_55 | ~spl6_63 | spl6_69 | ~spl6_70 | ~spl6_413)),
% 12.55/1.99    inference(forward_demodulation,[],[f13253,f592])).
% 12.55/1.99  fof(f13253,plain,(
% 12.55/1.99    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_55 | ~spl6_63 | spl6_69 | ~spl6_70 | ~spl6_413)),
% 12.55/1.99    inference(subsumption_resolution,[],[f13252,f641])).
% 12.55/1.99  fof(f13252,plain,(
% 12.55/1.99    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_63 | spl6_69 | ~spl6_70 | ~spl6_413)),
% 12.55/1.99    inference(forward_demodulation,[],[f13251,f9690])).
% 12.55/1.99  fof(f9690,plain,(
% 12.55/1.99    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_413),
% 12.55/1.99    inference(avatar_component_clause,[],[f9688])).
% 12.55/1.99  fof(f9688,plain,(
% 12.55/1.99    spl6_413 <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 12.55/1.99    introduced(avatar_definition,[new_symbols(naming,[spl6_413])])).
% 12.55/1.99  fof(f13251,plain,(
% 12.55/1.99    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_63 | spl6_69 | ~spl6_70)),
% 12.55/1.99    inference(forward_demodulation,[],[f13250,f592])).
% 12.55/1.99  fof(f13250,plain,(
% 12.55/1.99    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_63 | spl6_69 | ~spl6_70)),
% 12.55/1.99    inference(subsumption_resolution,[],[f13249,f740])).
% 12.55/1.99  fof(f740,plain,(
% 12.55/1.99    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | spl6_69),
% 12.55/1.99    inference(avatar_component_clause,[],[f739])).
% 12.55/1.99  fof(f739,plain,(
% 12.55/1.99    spl6_69 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)),
% 12.55/1.99    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 12.55/1.99  fof(f13249,plain,(
% 12.55/1.99    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_63 | ~spl6_70)),
% 12.55/1.99    inference(forward_demodulation,[],[f13248,f592])).
% 12.55/1.99  fof(f13248,plain,(
% 12.55/1.99    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_63 | ~spl6_70)),
% 12.55/1.99    inference(subsumption_resolution,[],[f13247,f681])).
% 12.55/1.99  fof(f681,plain,(
% 12.55/1.99    v1_partfun1(sK2,k1_relat_1(sK2)) | ~spl6_63),
% 12.55/1.99    inference(avatar_component_clause,[],[f679])).
% 12.55/1.99  fof(f679,plain,(
% 12.55/1.99    spl6_63 <=> v1_partfun1(sK2,k1_relat_1(sK2))),
% 12.55/1.99    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 12.55/1.99  fof(f13247,plain,(
% 12.55/1.99    ~v1_partfun1(sK2,k1_relat_1(sK2)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_70)),
% 12.55/1.99    inference(forward_demodulation,[],[f13246,f592])).
% 12.55/1.99  fof(f13246,plain,(
% 12.55/1.99    ~v1_partfun1(sK2,u1_struct_0(sK0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_70)),
% 12.55/1.99    inference(subsumption_resolution,[],[f13245,f127])).
% 12.55/1.99  fof(f127,plain,(
% 12.55/1.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 12.55/1.99    inference(cnf_transformation,[],[f53])).
% 12.55/1.99  fof(f53,plain,(
% 12.55/1.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.55/1.99    inference(ennf_transformation,[],[f29])).
% 12.55/1.99  fof(f29,plain,(
% 12.55/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 12.55/1.99    inference(pure_predicate_removal,[],[f13])).
% 12.55/1.99  fof(f13,axiom,(
% 12.55/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 12.55/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 12.55/1.99  fof(f13245,plain,(
% 12.55/1.99    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_70)),
% 12.55/1.99    inference(subsumption_resolution,[],[f13244,f212])).
% 12.55/1.99  fof(f212,plain,(
% 12.55/1.99    v2_pre_topc(sK0) | ~spl6_13),
% 12.55/1.99    inference(avatar_component_clause,[],[f210])).
% 12.55/1.99  fof(f210,plain,(
% 12.55/1.99    spl6_13 <=> v2_pre_topc(sK0)),
% 12.55/1.99    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 12.55/2.00  fof(f13244,plain,(
% 12.55/2.00    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_22 | ~spl6_70)),
% 12.55/2.00    inference(subsumption_resolution,[],[f13243,f207])).
% 12.55/2.00  fof(f207,plain,(
% 12.55/2.00    l1_pre_topc(sK0) | ~spl6_12),
% 12.55/2.00    inference(avatar_component_clause,[],[f205])).
% 12.55/2.00  fof(f205,plain,(
% 12.55/2.00    spl6_12 <=> l1_pre_topc(sK0)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 12.55/2.00  fof(f13243,plain,(
% 12.55/2.00    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_22 | ~spl6_70)),
% 12.55/2.00    inference(subsumption_resolution,[],[f13242,f202])).
% 12.55/2.00  fof(f202,plain,(
% 12.55/2.00    v2_pre_topc(sK1) | ~spl6_11),
% 12.55/2.00    inference(avatar_component_clause,[],[f200])).
% 12.55/2.00  fof(f200,plain,(
% 12.55/2.00    spl6_11 <=> v2_pre_topc(sK1)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 12.55/2.00  fof(f13242,plain,(
% 12.55/2.00    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_9 | ~spl6_10 | ~spl6_22 | ~spl6_70)),
% 12.55/2.00    inference(subsumption_resolution,[],[f13241,f197])).
% 12.55/2.00  fof(f197,plain,(
% 12.55/2.00    l1_pre_topc(sK1) | ~spl6_10),
% 12.55/2.00    inference(avatar_component_clause,[],[f195])).
% 12.55/2.00  fof(f195,plain,(
% 12.55/2.00    spl6_10 <=> l1_pre_topc(sK1)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 12.55/2.00  fof(f13241,plain,(
% 12.55/2.00    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_9 | ~spl6_22 | ~spl6_70)),
% 12.55/2.00    inference(subsumption_resolution,[],[f13240,f192])).
% 12.55/2.00  fof(f192,plain,(
% 12.55/2.00    v1_funct_1(sK2) | ~spl6_9),
% 12.55/2.00    inference(avatar_component_clause,[],[f190])).
% 12.55/2.00  fof(f190,plain,(
% 12.55/2.00    spl6_9 <=> v1_funct_1(sK2)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 12.55/2.00  fof(f13240,plain,(
% 12.55/2.00    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_1 | ~spl6_22 | ~spl6_70)),
% 12.55/2.00    inference(subsumption_resolution,[],[f13229,f151])).
% 12.55/2.00  fof(f151,plain,(
% 12.55/2.00    v5_pre_topc(sK2,sK0,sK1) | ~spl6_1),
% 12.55/2.00    inference(avatar_component_clause,[],[f150])).
% 12.55/2.00  fof(f150,plain,(
% 12.55/2.00    spl6_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 12.55/2.00  fof(f13229,plain,(
% 12.55/2.00    ~v1_partfun1(sK2,u1_struct_0(sK0)) | ~v4_relat_1(sK2,u1_struct_0(sK0)) | ~v5_pre_topc(sK2,sK0,sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_22 | ~spl6_70)),
% 12.55/2.00    inference(resolution,[],[f9761,f147])).
% 12.55/2.00  fof(f147,plain,(
% 12.55/2.00    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(duplicate_literal_removal,[],[f132])).
% 12.55/2.00  fof(f132,plain,(
% 12.55/2.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(equality_resolution,[],[f90])).
% 12.55/2.00  fof(f90,plain,(
% 12.55/2.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(cnf_transformation,[],[f63])).
% 12.55/2.00  fof(f63,plain,(
% 12.55/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.55/2.00    inference(nnf_transformation,[],[f33])).
% 12.55/2.00  fof(f33,plain,(
% 12.55/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.55/2.00    inference(flattening,[],[f32])).
% 12.55/2.00  fof(f32,plain,(
% 12.55/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.55/2.00    inference(ennf_transformation,[],[f23])).
% 12.55/2.00  fof(f23,axiom,(
% 12.55/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 12.55/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 12.55/2.00  fof(f9761,plain,(
% 12.55/2.00    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X1) | ~v4_relat_1(sK2,X1)) ) | (~spl6_22 | ~spl6_70)),
% 12.55/2.00    inference(subsumption_resolution,[],[f9747,f277])).
% 12.55/2.00  fof(f277,plain,(
% 12.55/2.00    v1_relat_1(sK2) | ~spl6_22),
% 12.55/2.00    inference(avatar_component_clause,[],[f275])).
% 12.55/2.00  fof(f275,plain,(
% 12.55/2.00    spl6_22 <=> v1_relat_1(sK2)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 12.55/2.00  fof(f9747,plain,(
% 12.55/2.00    ( ! [X1] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X1) | ~v4_relat_1(sK2,X1) | ~v1_relat_1(sK2)) ) | ~spl6_70),
% 12.55/2.00    inference(superposition,[],[f744,f107])).
% 12.55/2.00  fof(f107,plain,(
% 12.55/2.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 12.55/2.00    inference(cnf_transformation,[],[f70])).
% 12.55/2.00  fof(f70,plain,(
% 12.55/2.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 12.55/2.00    inference(nnf_transformation,[],[f40])).
% 12.55/2.00  fof(f40,plain,(
% 12.55/2.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 12.55/2.00    inference(flattening,[],[f39])).
% 12.55/2.00  fof(f39,plain,(
% 12.55/2.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 12.55/2.00    inference(ennf_transformation,[],[f18])).
% 12.55/2.00  fof(f18,axiom,(
% 12.55/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 12.55/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 12.55/2.00  fof(f744,plain,(
% 12.55/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~spl6_70),
% 12.55/2.00    inference(avatar_component_clause,[],[f743])).
% 12.55/2.00  fof(f743,plain,(
% 12.55/2.00    spl6_70 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 12.55/2.00  fof(f12466,plain,(
% 12.55/2.00    ~spl6_56 | spl6_2 | ~spl6_3 | ~spl6_52),
% 12.55/2.00    inference(avatar_split_clause,[],[f12465,f590,f160,f154,f644])).
% 12.55/2.00  fof(f644,plain,(
% 12.55/2.00    spl6_56 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 12.55/2.00  fof(f154,plain,(
% 12.55/2.00    spl6_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 12.55/2.00  fof(f160,plain,(
% 12.55/2.00    spl6_3 <=> sK2 = sK3),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 12.55/2.00  fof(f12465,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_2 | ~spl6_3 | ~spl6_52)),
% 12.55/2.00    inference(forward_demodulation,[],[f12464,f162])).
% 12.55/2.00  fof(f162,plain,(
% 12.55/2.00    sK2 = sK3 | ~spl6_3),
% 12.55/2.00    inference(avatar_component_clause,[],[f160])).
% 12.55/2.00  fof(f12464,plain,(
% 12.55/2.00    ~v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_2 | ~spl6_52)),
% 12.55/2.00    inference(forward_demodulation,[],[f156,f592])).
% 12.55/2.00  fof(f156,plain,(
% 12.55/2.00    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_2),
% 12.55/2.00    inference(avatar_component_clause,[],[f154])).
% 12.55/2.00  fof(f12459,plain,(
% 12.55/2.00    spl6_1 | ~spl6_64 | ~spl6_62 | ~spl6_69 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55),
% 12.55/2.00    inference(avatar_split_clause,[],[f12458,f639,f634,f590,f275,f210,f205,f200,f195,f190,f739,f674,f684,f150])).
% 12.55/2.00  fof(f684,plain,(
% 12.55/2.00    spl6_64 <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 12.55/2.00  fof(f674,plain,(
% 12.55/2.00    spl6_62 <=> v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 12.55/2.00  fof(f12458,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | v5_pre_topc(sK2,sK0,sK1) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55)),
% 12.55/2.00    inference(subsumption_resolution,[],[f12457,f212])).
% 12.55/2.00  fof(f12457,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | v5_pre_topc(sK2,sK0,sK1) | ~v2_pre_topc(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55)),
% 12.55/2.00    inference(subsumption_resolution,[],[f12456,f207])).
% 12.55/2.00  fof(f12456,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55)),
% 12.55/2.00    inference(subsumption_resolution,[],[f12455,f641])).
% 12.55/2.00  fof(f12455,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55)),
% 12.55/2.00    inference(subsumption_resolution,[],[f12407,f636])).
% 12.55/2.00  fof(f12407,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_22 | ~spl6_52 | ~spl6_54 | ~spl6_55)),
% 12.55/2.00    inference(superposition,[],[f8958,f592])).
% 12.55/2.00  fof(f8958,plain,(
% 12.55/2.00    ( ! [X5] : (~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | v5_pre_topc(sK2,X5,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_22 | ~spl6_54 | ~spl6_55)),
% 12.55/2.00    inference(subsumption_resolution,[],[f8957,f7902])).
% 12.55/2.00  fof(f7902,plain,(
% 12.55/2.00    ( ! [X0] : (v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (~spl6_22 | ~spl6_55)),
% 12.55/2.00    inference(subsumption_resolution,[],[f7901,f277])).
% 12.55/2.00  fof(f7901,plain,(
% 12.55/2.00    ( ! [X0] : (v1_funct_2(sK2,X0,u1_struct_0(sK1)) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl6_55),
% 12.55/2.00    inference(superposition,[],[f641,f107])).
% 12.55/2.00  fof(f8957,plain,(
% 12.55/2.00    ( ! [X5] : (~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1) | v5_pre_topc(sK2,X5,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1)) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_22 | ~spl6_54)),
% 12.55/2.00    inference(subsumption_resolution,[],[f8956,f202])).
% 12.55/2.00  fof(f8956,plain,(
% 12.55/2.00    ( ! [X5] : (~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1) | v5_pre_topc(sK2,X5,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl6_9 | ~spl6_10 | ~spl6_22 | ~spl6_54)),
% 12.55/2.00    inference(subsumption_resolution,[],[f8955,f197])).
% 12.55/2.00  fof(f8955,plain,(
% 12.55/2.00    ( ! [X5] : (~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1) | v5_pre_topc(sK2,X5,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl6_9 | ~spl6_22 | ~spl6_54)),
% 12.55/2.00    inference(subsumption_resolution,[],[f8947,f192])).
% 12.55/2.00  fof(f8947,plain,(
% 12.55/2.00    ( ! [X5] : (~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | ~v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)),sK1) | v5_pre_topc(sK2,X5,sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(X5),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) ) | (~spl6_22 | ~spl6_54)),
% 12.55/2.00    inference(resolution,[],[f7929,f148])).
% 12.55/2.00  fof(f148,plain,(
% 12.55/2.00    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(duplicate_literal_removal,[],[f131])).
% 12.55/2.00  fof(f131,plain,(
% 12.55/2.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(equality_resolution,[],[f91])).
% 12.55/2.00  fof(f91,plain,(
% 12.55/2.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(cnf_transformation,[],[f63])).
% 12.55/2.00  fof(f7929,plain,(
% 12.55/2.00    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0)) ) | (~spl6_22 | ~spl6_54)),
% 12.55/2.00    inference(subsumption_resolution,[],[f7924,f277])).
% 12.55/2.00  fof(f7924,plain,(
% 12.55/2.00    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) | ~v1_partfun1(sK2,X0) | ~v4_relat_1(sK2,X0) | ~v1_relat_1(sK2)) ) | ~spl6_54),
% 12.55/2.00    inference(superposition,[],[f636,f107])).
% 12.55/2.00  fof(f10543,plain,(
% 12.55/2.00    ~spl6_228 | spl6_40 | spl6_232),
% 12.55/2.00    inference(avatar_split_clause,[],[f10540,f3393,f484,f3323])).
% 12.55/2.00  fof(f3323,plain,(
% 12.55/2.00    spl6_228 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_228])])).
% 12.55/2.00  fof(f484,plain,(
% 12.55/2.00    spl6_40 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 12.55/2.00  fof(f3393,plain,(
% 12.55/2.00    spl6_232 <=> u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_232])])).
% 12.55/2.00  fof(f10540,plain,(
% 12.55/2.00    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl6_40 | spl6_232)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10537,f485])).
% 12.55/2.00  fof(f485,plain,(
% 12.55/2.00    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_40),
% 12.55/2.00    inference(avatar_component_clause,[],[f484])).
% 12.55/2.00  fof(f10537,plain,(
% 12.55/2.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl6_232),
% 12.55/2.00    inference(trivial_inequality_removal,[],[f10535])).
% 12.55/2.00  fof(f10535,plain,(
% 12.55/2.00    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl6_232),
% 12.55/2.00    inference(superposition,[],[f3394,f463])).
% 12.55/2.00  fof(f463,plain,(
% 12.55/2.00    ( ! [X2,X1] : (k1_relset_1(X1,X2,k1_xboole_0) = X1 | k1_xboole_0 = X2 | ~v1_funct_2(k1_xboole_0,X1,X2)) )),
% 12.55/2.00    inference(resolution,[],[f94,f118])).
% 12.55/2.00  fof(f118,plain,(
% 12.55/2.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 12.55/2.00    inference(cnf_transformation,[],[f7])).
% 12.55/2.00  fof(f7,axiom,(
% 12.55/2.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 12.55/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 12.55/2.00  fof(f94,plain,(
% 12.55/2.00    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 12.55/2.00    inference(cnf_transformation,[],[f65])).
% 12.55/2.00  fof(f65,plain,(
% 12.55/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.55/2.00    inference(nnf_transformation,[],[f37])).
% 12.55/2.00  fof(f37,plain,(
% 12.55/2.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.55/2.00    inference(flattening,[],[f36])).
% 12.55/2.00  fof(f36,plain,(
% 12.55/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.55/2.00    inference(ennf_transformation,[],[f17])).
% 12.55/2.00  fof(f17,axiom,(
% 12.55/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 12.55/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 12.55/2.00  fof(f3394,plain,(
% 12.55/2.00    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0) | spl6_232),
% 12.55/2.00    inference(avatar_component_clause,[],[f3393])).
% 12.55/2.00  fof(f10227,plain,(
% 12.55/2.00    spl6_56 | ~spl6_2 | ~spl6_3 | ~spl6_52),
% 12.55/2.00    inference(avatar_split_clause,[],[f10226,f590,f160,f154,f644])).
% 12.55/2.00  fof(f10226,plain,(
% 12.55/2.00    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_52)),
% 12.55/2.00    inference(forward_demodulation,[],[f10225,f162])).
% 12.55/2.00  fof(f10225,plain,(
% 12.55/2.00    v5_pre_topc(sK3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_52)),
% 12.55/2.00    inference(forward_demodulation,[],[f155,f592])).
% 12.55/2.00  fof(f155,plain,(
% 12.55/2.00    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_2),
% 12.55/2.00    inference(avatar_component_clause,[],[f154])).
% 12.55/2.00  fof(f10098,plain,(
% 12.55/2.00    spl6_69 | ~spl6_56 | ~spl6_398 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_54 | ~spl6_55 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413),
% 12.55/2.00    inference(avatar_split_clause,[],[f10097,f9688,f699,f694,f654,f639,f634,f200,f195,f190,f8930,f644,f739])).
% 12.55/2.00  fof(f8930,plain,(
% 12.55/2.00    spl6_398 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_398])])).
% 12.55/2.00  fof(f654,plain,(
% 12.55/2.00    spl6_58 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 12.55/2.00  fof(f694,plain,(
% 12.55/2.00    spl6_66 <=> v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 12.55/2.00  fof(f699,plain,(
% 12.55/2.00    spl6_67 <=> l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 12.55/2.00  fof(f10097,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_54 | ~spl6_55 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10096,f641])).
% 12.55/2.00  fof(f10096,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_54 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(forward_demodulation,[],[f10095,f9690])).
% 12.55/2.00  fof(f10095,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_54 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10094,f636])).
% 12.55/2.00  fof(f10094,plain,(
% 12.55/2.00    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(forward_demodulation,[],[f10093,f9690])).
% 12.55/2.00  fof(f10093,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(forward_demodulation,[],[f10092,f9690])).
% 12.55/2.00  fof(f10092,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58 | ~spl6_66 | ~spl6_67)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10091,f696])).
% 12.55/2.00  fof(f696,plain,(
% 12.55/2.00    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_66),
% 12.55/2.00    inference(avatar_component_clause,[],[f694])).
% 12.55/2.00  fof(f10091,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58 | ~spl6_67)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10090,f700])).
% 12.55/2.00  fof(f700,plain,(
% 12.55/2.00    l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_67),
% 12.55/2.00    inference(avatar_component_clause,[],[f699])).
% 12.55/2.00  fof(f10090,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10089,f202])).
% 12.55/2.00  fof(f10089,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_58)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10088,f197])).
% 12.55/2.00  fof(f10088,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_58)),
% 12.55/2.00    inference(subsumption_resolution,[],[f8314,f192])).
% 12.55/2.00  fof(f8314,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_58),
% 12.55/2.00    inference(resolution,[],[f656,f146])).
% 12.55/2.00  fof(f146,plain,(
% 12.55/2.00    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(duplicate_literal_removal,[],[f133])).
% 12.55/2.00  fof(f133,plain,(
% 12.55/2.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(equality_resolution,[],[f93])).
% 12.55/2.00  fof(f93,plain,(
% 12.55/2.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(cnf_transformation,[],[f64])).
% 12.55/2.00  fof(f64,plain,(
% 12.55/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.55/2.00    inference(nnf_transformation,[],[f35])).
% 12.55/2.00  fof(f35,plain,(
% 12.55/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.55/2.00    inference(flattening,[],[f34])).
% 12.55/2.00  fof(f34,plain,(
% 12.55/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.55/2.00    inference(ennf_transformation,[],[f24])).
% 12.55/2.00  fof(f24,axiom,(
% 12.55/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 12.55/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 12.55/2.00  fof(f656,plain,(
% 12.55/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_58),
% 12.55/2.00    inference(avatar_component_clause,[],[f654])).
% 12.55/2.00  fof(f10087,plain,(
% 12.55/2.00    spl6_56 | ~spl6_69 | ~spl6_398 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_54 | ~spl6_55 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413),
% 12.55/2.00    inference(avatar_split_clause,[],[f10086,f9688,f699,f694,f654,f639,f634,f200,f195,f190,f8930,f739,f644])).
% 12.55/2.00  fof(f10086,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_54 | ~spl6_55 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10085,f641])).
% 12.55/2.00  fof(f10085,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_54 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(forward_demodulation,[],[f10084,f9690])).
% 12.55/2.00  fof(f10084,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_54 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10083,f636])).
% 12.55/2.00  fof(f10083,plain,(
% 12.55/2.00    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(forward_demodulation,[],[f10082,f9690])).
% 12.55/2.00  fof(f10082,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58 | ~spl6_66 | ~spl6_67 | ~spl6_413)),
% 12.55/2.00    inference(forward_demodulation,[],[f10081,f9690])).
% 12.55/2.00  fof(f10081,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58 | ~spl6_66 | ~spl6_67)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10080,f696])).
% 12.55/2.00  fof(f10080,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58 | ~spl6_67)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10079,f700])).
% 12.55/2.00  fof(f10079,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_58)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10078,f202])).
% 12.55/2.00  fof(f10078,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_58)),
% 12.55/2.00    inference(subsumption_resolution,[],[f10077,f197])).
% 12.55/2.00  fof(f10077,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_58)),
% 12.55/2.00    inference(subsumption_resolution,[],[f8315,f192])).
% 12.55/2.00  fof(f8315,plain,(
% 12.55/2.00    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl6_58),
% 12.55/2.00    inference(resolution,[],[f656,f145])).
% 12.55/2.00  fof(f145,plain,(
% 12.55/2.00    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(duplicate_literal_removal,[],[f134])).
% 12.55/2.00  fof(f134,plain,(
% 12.55/2.00    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(equality_resolution,[],[f92])).
% 12.55/2.00  fof(f92,plain,(
% 12.55/2.00    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.00    inference(cnf_transformation,[],[f64])).
% 12.55/2.00  fof(f9842,plain,(
% 12.55/2.00    spl6_398 | ~spl6_57 | ~spl6_413),
% 12.55/2.00    inference(avatar_split_clause,[],[f9762,f9688,f649,f8930])).
% 12.55/2.00  fof(f649,plain,(
% 12.55/2.00    spl6_57 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 12.55/2.00  fof(f9762,plain,(
% 12.55/2.00    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_57 | ~spl6_413)),
% 12.55/2.00    inference(backward_demodulation,[],[f651,f9690])).
% 12.55/2.00  fof(f651,plain,(
% 12.55/2.00    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_57),
% 12.55/2.00    inference(avatar_component_clause,[],[f649])).
% 12.55/2.00  fof(f9707,plain,(
% 12.55/2.00    spl6_64 | ~spl6_34 | ~spl6_52),
% 12.55/2.00    inference(avatar_split_clause,[],[f9706,f590,f448,f684])).
% 12.55/2.00  fof(f448,plain,(
% 12.55/2.00    spl6_34 <=> v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 12.55/2.00  fof(f9706,plain,(
% 12.55/2.00    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | (~spl6_34 | ~spl6_52)),
% 12.55/2.00    inference(forward_demodulation,[],[f450,f592])).
% 12.55/2.00  fof(f450,plain,(
% 12.55/2.00    v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl6_34),
% 12.55/2.00    inference(avatar_component_clause,[],[f448])).
% 12.55/2.00  fof(f9699,plain,(
% 12.55/2.00    k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | u1_struct_0(sK0) != k1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 12.55/2.00    introduced(theory_tautology_sat_conflict,[])).
% 12.55/2.00  fof(f9698,plain,(
% 12.55/2.00    u1_struct_0(sK0) != k1_relat_1(sK2) | k1_relat_1(sK2) != u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~v1_partfun1(sK2,u1_struct_0(sK0))),
% 12.55/2.00    introduced(theory_tautology_sat_conflict,[])).
% 12.55/2.00  fof(f9693,plain,(
% 12.55/2.00    spl6_413 | ~spl6_58 | ~spl6_72),
% 12.55/2.00    inference(avatar_split_clause,[],[f9692,f817,f654,f9688])).
% 12.55/2.00  fof(f817,plain,(
% 12.55/2.00    spl6_72 <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 12.55/2.00  fof(f9692,plain,(
% 12.55/2.00    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_58 | ~spl6_72)),
% 12.55/2.00    inference(subsumption_resolution,[],[f9683,f656])).
% 12.55/2.00  fof(f9683,plain,(
% 12.55/2.00    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_72),
% 12.55/2.00    inference(superposition,[],[f100,f819])).
% 12.55/2.00  fof(f819,plain,(
% 12.55/2.00    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl6_72),
% 12.55/2.00    inference(avatar_component_clause,[],[f817])).
% 12.55/2.00  fof(f100,plain,(
% 12.55/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.55/2.00    inference(cnf_transformation,[],[f38])).
% 12.55/2.00  fof(f38,plain,(
% 12.55/2.00    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.55/2.00    inference(ennf_transformation,[],[f15])).
% 12.55/2.00  fof(f15,axiom,(
% 12.55/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 12.55/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 12.55/2.00  fof(f8708,plain,(
% 12.55/2.00    spl6_72 | spl6_40 | ~spl6_57 | ~spl6_58),
% 12.55/2.00    inference(avatar_split_clause,[],[f8707,f654,f649,f484,f817])).
% 12.55/2.00  fof(f8707,plain,(
% 12.55/2.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl6_57 | ~spl6_58)),
% 12.55/2.00    inference(subsumption_resolution,[],[f8690,f651])).
% 12.55/2.00  fof(f8690,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl6_58),
% 12.55/2.00    inference(resolution,[],[f656,f94])).
% 12.55/2.00  fof(f8430,plain,(
% 12.55/2.00    ~spl6_40 | ~spl6_58 | spl6_73),
% 12.55/2.00    inference(avatar_contradiction_clause,[],[f8429])).
% 12.55/2.00  fof(f8429,plain,(
% 12.55/2.00    $false | (~spl6_40 | ~spl6_58 | spl6_73)),
% 12.55/2.00    inference(subsumption_resolution,[],[f8428,f883])).
% 12.55/2.00  fof(f883,plain,(
% 12.55/2.00    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl6_73),
% 12.55/2.00    inference(avatar_component_clause,[],[f882])).
% 12.55/2.00  fof(f882,plain,(
% 12.55/2.00    spl6_73 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 12.55/2.00  fof(f8428,plain,(
% 12.55/2.00    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_40 | ~spl6_58)),
% 12.55/2.00    inference(forward_demodulation,[],[f8362,f140])).
% 12.55/2.00  fof(f140,plain,(
% 12.55/2.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 12.55/2.00    inference(equality_resolution,[],[f103])).
% 12.55/2.00  fof(f103,plain,(
% 12.55/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 12.55/2.00    inference(cnf_transformation,[],[f67])).
% 12.55/2.00  fof(f67,plain,(
% 12.55/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 12.55/2.00    inference(flattening,[],[f66])).
% 12.55/2.00  fof(f66,plain,(
% 12.55/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 12.55/2.00    inference(nnf_transformation,[],[f5])).
% 12.55/2.00  fof(f5,axiom,(
% 12.55/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 12.55/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 12.55/2.00  fof(f8362,plain,(
% 12.55/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl6_40 | ~spl6_58)),
% 12.55/2.00    inference(backward_demodulation,[],[f656,f486])).
% 12.55/2.00  fof(f486,plain,(
% 12.55/2.00    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_40),
% 12.55/2.00    inference(avatar_component_clause,[],[f484])).
% 12.55/2.00  fof(f8360,plain,(
% 12.55/2.00    spl6_62 | ~spl6_27 | ~spl6_52),
% 12.55/2.00    inference(avatar_split_clause,[],[f8359,f590,f325,f674])).
% 12.55/2.00  fof(f325,plain,(
% 12.55/2.00    spl6_27 <=> v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 12.55/2.00  fof(f8359,plain,(
% 12.55/2.00    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))) | (~spl6_27 | ~spl6_52)),
% 12.55/2.00    inference(forward_demodulation,[],[f327,f592])).
% 12.55/2.00  fof(f327,plain,(
% 12.55/2.00    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl6_27),
% 12.55/2.00    inference(avatar_component_clause,[],[f325])).
% 12.55/2.00  fof(f8313,plain,(
% 12.55/2.00    spl6_58 | ~spl6_17 | ~spl6_52),
% 12.55/2.00    inference(avatar_split_clause,[],[f8312,f590,f234,f654])).
% 12.55/2.00  fof(f234,plain,(
% 12.55/2.00    spl6_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 12.55/2.00  fof(f8312,plain,(
% 12.55/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_17 | ~spl6_52)),
% 12.55/2.00    inference(forward_demodulation,[],[f236,f592])).
% 12.55/2.00  fof(f236,plain,(
% 12.55/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_17),
% 12.55/2.00    inference(avatar_component_clause,[],[f234])).
% 12.55/2.00  fof(f8301,plain,(
% 12.55/2.00    spl6_57 | ~spl6_16 | ~spl6_52),
% 12.55/2.00    inference(avatar_split_clause,[],[f8300,f590,f228,f649])).
% 12.55/2.00  fof(f228,plain,(
% 12.55/2.00    spl6_16 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 12.55/2.00  fof(f8300,plain,(
% 12.55/2.00    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_16 | ~spl6_52)),
% 12.55/2.00    inference(forward_demodulation,[],[f230,f592])).
% 12.55/2.00  fof(f230,plain,(
% 12.55/2.00    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_16),
% 12.55/2.00    inference(avatar_component_clause,[],[f228])).
% 12.55/2.00  fof(f8150,plain,(
% 12.55/2.00    spl6_67 | ~spl6_12 | ~spl6_52),
% 12.55/2.00    inference(avatar_split_clause,[],[f8149,f590,f205,f699])).
% 12.55/2.00  fof(f8149,plain,(
% 12.55/2.00    l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_12 | ~spl6_52)),
% 12.55/2.00    inference(subsumption_resolution,[],[f7996,f207])).
% 12.55/2.00  fof(f7996,plain,(
% 12.55/2.00    l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~spl6_52),
% 12.55/2.00    inference(superposition,[],[f292,f592])).
% 12.55/2.00  fof(f292,plain,(
% 12.55/2.00    ( ! [X0] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 12.55/2.00    inference(resolution,[],[f111,f109])).
% 12.55/2.00  fof(f109,plain,(
% 12.55/2.00    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 12.55/2.00    inference(cnf_transformation,[],[f41])).
% 12.55/2.00  fof(f41,plain,(
% 12.55/2.00    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 12.55/2.00    inference(ennf_transformation,[],[f28])).
% 12.55/2.00  fof(f28,plain,(
% 12.55/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 12.55/2.00    inference(pure_predicate_removal,[],[f20])).
% 12.55/2.00  fof(f20,axiom,(
% 12.55/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 12.55/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 12.55/2.00  fof(f111,plain,(
% 12.55/2.00    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 12.55/2.00    inference(cnf_transformation,[],[f44])).
% 12.55/2.00  fof(f44,plain,(
% 12.55/2.00    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.55/2.00    inference(ennf_transformation,[],[f21])).
% 12.55/2.00  fof(f21,axiom,(
% 12.55/2.00    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 12.55/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 12.55/2.00  fof(f8030,plain,(
% 12.55/2.00    spl6_66 | ~spl6_42 | ~spl6_52),
% 12.55/2.00    inference(avatar_split_clause,[],[f7961,f590,f513,f694])).
% 12.55/2.00  fof(f513,plain,(
% 12.55/2.00    spl6_42 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 12.55/2.00  fof(f7961,plain,(
% 12.55/2.00    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_42 | ~spl6_52)),
% 12.55/2.00    inference(backward_demodulation,[],[f514,f592])).
% 12.55/2.00  fof(f514,plain,(
% 12.55/2.00    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_42),
% 12.55/2.00    inference(avatar_component_clause,[],[f513])).
% 12.55/2.00  fof(f7953,plain,(
% 12.55/2.00    spl6_77 | ~spl6_36 | ~spl6_104 | spl6_110),
% 12.55/2.00    inference(avatar_split_clause,[],[f7952,f1255,f1178,f457,f902])).
% 12.55/2.00  fof(f902,plain,(
% 12.55/2.00    spl6_77 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 12.55/2.00  fof(f457,plain,(
% 12.55/2.00    spl6_36 <=> ! [X1,X2] : (~v1_funct_2(k1_xboole_0,X1,X2) | v1_xboole_0(X2) | v1_partfun1(k1_xboole_0,X1))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 12.55/2.00  fof(f1178,plain,(
% 12.55/2.00    spl6_104 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).
% 12.55/2.00  fof(f1255,plain,(
% 12.55/2.00    spl6_110 <=> v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).
% 12.55/2.00  fof(f7952,plain,(
% 12.55/2.00    v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_36 | ~spl6_104 | spl6_110)),
% 12.55/2.00    inference(subsumption_resolution,[],[f7951,f1256])).
% 12.55/2.00  fof(f1256,plain,(
% 12.55/2.00    ~v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | spl6_110),
% 12.55/2.00    inference(avatar_component_clause,[],[f1255])).
% 12.55/2.00  fof(f7951,plain,(
% 12.55/2.00    v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (~spl6_36 | ~spl6_104)),
% 12.55/2.00    inference(resolution,[],[f1180,f458])).
% 12.55/2.00  fof(f458,plain,(
% 12.55/2.00    ( ! [X2,X1] : (~v1_funct_2(k1_xboole_0,X1,X2) | v1_xboole_0(X2) | v1_partfun1(k1_xboole_0,X1)) ) | ~spl6_36),
% 12.55/2.00    inference(avatar_component_clause,[],[f457])).
% 12.55/2.00  fof(f1180,plain,(
% 12.55/2.00    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_104),
% 12.55/2.00    inference(avatar_component_clause,[],[f1178])).
% 12.55/2.00  fof(f7946,plain,(
% 12.55/2.00    spl6_63 | ~spl6_22 | ~spl6_61),
% 12.55/2.00    inference(avatar_split_clause,[],[f7945,f669,f275,f679])).
% 12.55/2.00  fof(f669,plain,(
% 12.55/2.00    spl6_61 <=> v4_relat_1(sK2,k1_relat_1(sK2))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 12.55/2.00  fof(f7945,plain,(
% 12.55/2.00    v1_partfun1(sK2,k1_relat_1(sK2)) | (~spl6_22 | ~spl6_61)),
% 12.55/2.00    inference(subsumption_resolution,[],[f7943,f277])).
% 12.55/2.00  fof(f7943,plain,(
% 12.55/2.00    v1_partfun1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl6_61),
% 12.55/2.00    inference(resolution,[],[f671,f144])).
% 12.55/2.00  fof(f144,plain,(
% 12.55/2.00    ( ! [X1] : (~v4_relat_1(X1,k1_relat_1(X1)) | v1_partfun1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 12.55/2.00    inference(equality_resolution,[],[f108])).
% 12.55/2.00  fof(f108,plain,(
% 12.55/2.00    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 12.55/2.00    inference(cnf_transformation,[],[f70])).
% 12.55/2.00  fof(f671,plain,(
% 12.55/2.00    v4_relat_1(sK2,k1_relat_1(sK2)) | ~spl6_61),
% 12.55/2.00    inference(avatar_component_clause,[],[f669])).
% 12.55/2.00  fof(f7914,plain,(
% 12.55/2.00    spl6_26 | ~spl6_7),
% 12.55/2.00    inference(avatar_split_clause,[],[f7907,f180,f320])).
% 12.55/2.00  fof(f320,plain,(
% 12.55/2.00    spl6_26 <=> v4_relat_1(sK2,u1_struct_0(sK0))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 12.55/2.00  fof(f180,plain,(
% 12.55/2.00    spl6_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 12.55/2.00  fof(f7907,plain,(
% 12.55/2.00    v4_relat_1(sK2,u1_struct_0(sK0)) | ~spl6_7),
% 12.55/2.00    inference(resolution,[],[f182,f127])).
% 12.55/2.00  fof(f182,plain,(
% 12.55/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_7),
% 12.55/2.00    inference(avatar_component_clause,[],[f180])).
% 12.55/2.00  fof(f7913,plain,(
% 12.55/2.00    spl6_37 | spl6_38 | ~spl6_7 | ~spl6_8),
% 12.55/2.00    inference(avatar_split_clause,[],[f7912,f185,f180,f474,f470])).
% 12.55/2.00  fof(f470,plain,(
% 12.55/2.00    spl6_37 <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 12.55/2.00  fof(f474,plain,(
% 12.55/2.00    spl6_38 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 12.55/2.00  fof(f185,plain,(
% 12.55/2.00    spl6_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 12.55/2.00    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 12.55/2.00  fof(f7912,plain,(
% 12.55/2.00    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl6_7 | ~spl6_8)),
% 12.55/2.00    inference(subsumption_resolution,[],[f7904,f187])).
% 12.55/2.00  fof(f187,plain,(
% 12.55/2.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl6_8),
% 12.55/2.00    inference(avatar_component_clause,[],[f185])).
% 12.55/2.00  fof(f7904,plain,(
% 12.55/2.00    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl6_7),
% 12.55/2.00    inference(resolution,[],[f182,f94])).
% 12.55/2.00  fof(f7887,plain,(
% 12.55/2.00    ~spl6_85 | ~spl6_3 | spl6_96),
% 12.55/2.00    inference(avatar_split_clause,[],[f7886,f1118,f160,f991])).
% 12.55/2.01  fof(f991,plain,(
% 12.55/2.01    spl6_85 <=> k1_xboole_0 = sK2),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 12.55/2.01  fof(f1118,plain,(
% 12.55/2.01    spl6_96 <=> k1_xboole_0 = sK3),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).
% 12.55/2.01  fof(f7886,plain,(
% 12.55/2.01    k1_xboole_0 != sK2 | (~spl6_3 | spl6_96)),
% 12.55/2.01    inference(superposition,[],[f1119,f162])).
% 12.55/2.01  fof(f1119,plain,(
% 12.55/2.01    k1_xboole_0 != sK3 | spl6_96),
% 12.55/2.01    inference(avatar_component_clause,[],[f1118])).
% 12.55/2.01  fof(f7825,plain,(
% 12.55/2.01    ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_41 | ~spl6_95 | ~spl6_97 | spl6_111 | ~spl6_230),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f7824])).
% 12.55/2.01  fof(f7824,plain,(
% 12.55/2.01    $false | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_41 | ~spl6_95 | ~spl6_97 | spl6_111 | ~spl6_230)),
% 12.55/2.01    inference(subsumption_resolution,[],[f7823,f1127])).
% 12.55/2.01  fof(f1127,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~spl6_97),
% 12.55/2.01    inference(avatar_component_clause,[],[f1125])).
% 12.55/2.01  fof(f1125,plain,(
% 12.55/2.01    spl6_97 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).
% 12.55/2.01  fof(f7823,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_41 | ~spl6_95 | spl6_111 | ~spl6_230)),
% 12.55/2.01    inference(subsumption_resolution,[],[f7822,f1115])).
% 12.55/2.01  fof(f1115,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl6_95),
% 12.55/2.01    inference(avatar_component_clause,[],[f1113])).
% 12.55/2.01  fof(f1113,plain,(
% 12.55/2.01    spl6_95 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).
% 12.55/2.01  fof(f7822,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_41 | spl6_111 | ~spl6_230)),
% 12.55/2.01    inference(subsumption_resolution,[],[f7821,f207])).
% 12.55/2.01  fof(f7821,plain,(
% 12.55/2.01    ~l1_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_38 | ~spl6_41 | spl6_111 | ~spl6_230)),
% 12.55/2.01    inference(subsumption_resolution,[],[f7819,f212])).
% 12.55/2.01  fof(f7819,plain,(
% 12.55/2.01    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_41 | spl6_111 | ~spl6_230)),
% 12.55/2.01    inference(resolution,[],[f7815,f1294])).
% 12.55/2.01  fof(f1294,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl6_111),
% 12.55/2.01    inference(avatar_component_clause,[],[f1293])).
% 12.55/2.01  fof(f1293,plain,(
% 12.55/2.01    spl6_111 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).
% 12.55/2.01  fof(f7815,plain,(
% 12.55/2.01    ( ! [X25] : (v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(X25) | ~l1_pre_topc(X25) | ~v5_pre_topc(k1_xboole_0,X25,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0)) ) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_41 | ~spl6_230)),
% 12.55/2.01    inference(duplicate_literal_removal,[],[f7814])).
% 12.55/2.01  fof(f7814,plain,(
% 12.55/2.01    ( ! [X25] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0) | ~v2_pre_topc(X25) | ~l1_pre_topc(X25) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X25,sK1) | v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_41 | ~spl6_230)),
% 12.55/2.01    inference(forward_demodulation,[],[f7298,f3362])).
% 12.55/2.01  fof(f3362,plain,(
% 12.55/2.01    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_230),
% 12.55/2.01    inference(avatar_component_clause,[],[f3360])).
% 12.55/2.01  fof(f3360,plain,(
% 12.55/2.01    spl6_230 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_230])])).
% 12.55/2.01  fof(f7298,plain,(
% 12.55/2.01    ( ! [X25] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X25),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(X25) | ~l1_pre_topc(X25) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X25,sK1) | v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_41)),
% 12.55/2.01    inference(subsumption_resolution,[],[f7297,f197])).
% 12.55/2.01  fof(f7297,plain,(
% 12.55/2.01    ( ! [X25] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X25),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(X25) | ~l1_pre_topc(X25) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X25,sK1) | v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ) | (~spl6_11 | ~spl6_38 | ~spl6_41)),
% 12.55/2.01    inference(subsumption_resolution,[],[f7214,f202])).
% 12.55/2.01  fof(f7214,plain,(
% 12.55/2.01    ( ! [X25] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X25),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(X25) | ~l1_pre_topc(X25) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X25),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X25,sK1) | v5_pre_topc(k1_xboole_0,X25,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ) | (~spl6_38 | ~spl6_41)),
% 12.55/2.01    inference(superposition,[],[f500,f476])).
% 12.55/2.01  fof(f476,plain,(
% 12.55/2.01    k1_xboole_0 = u1_struct_0(sK1) | ~spl6_38),
% 12.55/2.01    inference(avatar_component_clause,[],[f474])).
% 12.55/2.01  fof(f500,plain,(
% 12.55/2.01    ( ! [X2,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~v5_pre_topc(k1_xboole_0,X1,X2) | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) ) | ~spl6_41),
% 12.55/2.01    inference(avatar_component_clause,[],[f499])).
% 12.55/2.01  fof(f499,plain,(
% 12.55/2.01    spl6_41 <=> ! [X1,X2] : (~v5_pre_topc(k1_xboole_0,X1,X2) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 12.55/2.01  fof(f7737,plain,(
% 12.55/2.01    ~spl6_321 | ~spl6_103 | spl6_133),
% 12.55/2.01    inference(avatar_split_clause,[],[f7736,f1718,f1166,f6055])).
% 12.55/2.01  fof(f6055,plain,(
% 12.55/2.01    spl6_321 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_321])])).
% 12.55/2.01  fof(f1166,plain,(
% 12.55/2.01    spl6_103 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).
% 12.55/2.01  fof(f1718,plain,(
% 12.55/2.01    spl6_133 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).
% 12.55/2.01  fof(f7736,plain,(
% 12.55/2.01    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_103 | spl6_133)),
% 12.55/2.01    inference(forward_demodulation,[],[f1719,f1168])).
% 12.55/2.01  fof(f1168,plain,(
% 12.55/2.01    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_103),
% 12.55/2.01    inference(avatar_component_clause,[],[f1166])).
% 12.55/2.01  fof(f1719,plain,(
% 12.55/2.01    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0) | spl6_133),
% 12.55/2.01    inference(avatar_component_clause,[],[f1718])).
% 12.55/2.01  fof(f7502,plain,(
% 12.55/2.01    spl6_322 | ~spl6_104 | ~spl6_230),
% 12.55/2.01    inference(avatar_split_clause,[],[f7456,f3360,f1178,f6062])).
% 12.55/2.01  fof(f6062,plain,(
% 12.55/2.01    spl6_322 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_322])])).
% 12.55/2.01  fof(f7456,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_104 | ~spl6_230)),
% 12.55/2.01    inference(backward_demodulation,[],[f1180,f3362])).
% 12.55/2.01  fof(f7413,plain,(
% 12.55/2.01    spl6_217 | ~spl6_103),
% 12.55/2.01    inference(avatar_split_clause,[],[f7412,f1166,f3097])).
% 12.55/2.01  fof(f3097,plain,(
% 12.55/2.01    spl6_217 <=> ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_217])])).
% 12.55/2.01  fof(f7412,plain,(
% 12.55/2.01    ( ! [X1] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) ) | ~spl6_103),
% 12.55/2.01    inference(subsumption_resolution,[],[f7406,f118])).
% 12.55/2.01  fof(f7406,plain,(
% 12.55/2.01    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) ) | ~spl6_103),
% 12.55/2.01    inference(trivial_inequality_removal,[],[f7404])).
% 12.55/2.01  fof(f7404,plain,(
% 12.55/2.01    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X1)) ) | ~spl6_103),
% 12.55/2.01    inference(superposition,[],[f418,f1168])).
% 12.55/2.01  fof(f418,plain,(
% 12.55/2.01    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 12.55/2.01    inference(duplicate_literal_removal,[],[f417])).
% 12.55/2.01  fof(f417,plain,(
% 12.55/2.01    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 12.55/2.01    inference(forward_demodulation,[],[f416,f141])).
% 12.55/2.01  fof(f141,plain,(
% 12.55/2.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 12.55/2.01    inference(equality_resolution,[],[f102])).
% 12.55/2.01  fof(f102,plain,(
% 12.55/2.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 12.55/2.01    inference(cnf_transformation,[],[f67])).
% 12.55/2.01  fof(f416,plain,(
% 12.55/2.01    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 12.55/2.01    inference(superposition,[],[f415,f100])).
% 12.55/2.01  fof(f415,plain,(
% 12.55/2.01    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 12.55/2.01    inference(forward_demodulation,[],[f138,f141])).
% 12.55/2.01  fof(f138,plain,(
% 12.55/2.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 12.55/2.01    inference(equality_resolution,[],[f97])).
% 12.55/2.01  fof(f97,plain,(
% 12.55/2.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 12.55/2.01    inference(cnf_transformation,[],[f65])).
% 12.55/2.01  fof(f7157,plain,(
% 12.55/2.01    spl6_95 | ~spl6_1 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f7156,f991,f150,f1113])).
% 12.55/2.01  fof(f7156,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_1 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f151,f993])).
% 12.55/2.01  fof(f993,plain,(
% 12.55/2.01    k1_xboole_0 = sK2 | ~spl6_85),
% 12.55/2.01    inference(avatar_component_clause,[],[f991])).
% 12.55/2.01  fof(f7155,plain,(
% 12.55/2.01    ~spl6_219 | spl6_2 | ~spl6_96),
% 12.55/2.01    inference(avatar_split_clause,[],[f7154,f1118,f154,f3223])).
% 12.55/2.01  fof(f3223,plain,(
% 12.55/2.01    spl6_219 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_219])])).
% 12.55/2.01  fof(f7154,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_2 | ~spl6_96)),
% 12.55/2.01    inference(forward_demodulation,[],[f156,f1120])).
% 12.55/2.01  fof(f1120,plain,(
% 12.55/2.01    k1_xboole_0 = sK3 | ~spl6_96),
% 12.55/2.01    inference(avatar_component_clause,[],[f1118])).
% 12.55/2.01  fof(f7153,plain,(
% 12.55/2.01    ~spl6_219 | spl6_15 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f7152,f991,f222,f3223])).
% 12.55/2.01  fof(f222,plain,(
% 12.55/2.01    spl6_15 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 12.55/2.01  fof(f7152,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl6_15 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f223,f993])).
% 12.55/2.01  fof(f223,plain,(
% 12.55/2.01    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_15),
% 12.55/2.01    inference(avatar_component_clause,[],[f222])).
% 12.55/2.01  fof(f7142,plain,(
% 12.55/2.01    spl6_220 | ~spl6_44 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f7141,f991,f521,f3231])).
% 12.55/2.01  fof(f3231,plain,(
% 12.55/2.01    spl6_220 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_220])])).
% 12.55/2.01  fof(f521,plain,(
% 12.55/2.01    spl6_44 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 12.55/2.01  fof(f7141,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl6_44 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f522,f993])).
% 12.55/2.01  fof(f522,plain,(
% 12.55/2.01    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl6_44),
% 12.55/2.01    inference(avatar_component_clause,[],[f521])).
% 12.55/2.01  fof(f7140,plain,(
% 12.55/2.01    ~spl6_152 | spl6_46 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f7139,f991,f529,f1947])).
% 12.55/2.01  fof(f1947,plain,(
% 12.55/2.01    spl6_152 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_152])])).
% 12.55/2.01  fof(f529,plain,(
% 12.55/2.01    spl6_46 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 12.55/2.01  fof(f7139,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (spl6_46 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f530,f993])).
% 12.55/2.01  fof(f530,plain,(
% 12.55/2.01    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl6_46),
% 12.55/2.01    inference(avatar_component_clause,[],[f529])).
% 12.55/2.01  fof(f7123,plain,(
% 12.55/2.01    ~spl6_100 | ~spl6_96 | spl6_101),
% 12.55/2.01    inference(avatar_split_clause,[],[f7122,f1149,f1118,f1143])).
% 12.55/2.01  fof(f1143,plain,(
% 12.55/2.01    spl6_100 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 12.55/2.01  fof(f1149,plain,(
% 12.55/2.01    spl6_101 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).
% 12.55/2.01  fof(f7122,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_96 | spl6_101)),
% 12.55/2.01    inference(forward_demodulation,[],[f1150,f1120])).
% 12.55/2.01  fof(f1150,plain,(
% 12.55/2.01    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl6_101),
% 12.55/2.01    inference(avatar_component_clause,[],[f1149])).
% 12.55/2.01  fof(f7093,plain,(
% 12.55/2.01    spl6_100 | ~spl6_111 | ~spl6_112 | ~spl6_12 | ~spl6_13 | ~spl6_78 | ~spl6_79 | ~spl6_93 | ~spl6_104),
% 12.55/2.01    inference(avatar_split_clause,[],[f7092,f1178,f1088,f912,f907,f210,f205,f1297,f1293,f1143])).
% 12.55/2.01  fof(f1297,plain,(
% 12.55/2.01    spl6_112 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).
% 12.55/2.01  fof(f907,plain,(
% 12.55/2.01    spl6_78 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 12.55/2.01  fof(f912,plain,(
% 12.55/2.01    spl6_79 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 12.55/2.01  fof(f1088,plain,(
% 12.55/2.01    spl6_93 <=> ! [X1,X2] : (~v5_pre_topc(k1_xboole_0,X1,X2) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 12.55/2.01  fof(f7092,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_78 | ~spl6_79 | ~spl6_93 | ~spl6_104)),
% 12.55/2.01    inference(subsumption_resolution,[],[f7091,f913])).
% 12.55/2.01  fof(f913,plain,(
% 12.55/2.01    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_79),
% 12.55/2.01    inference(avatar_component_clause,[],[f912])).
% 12.55/2.01  fof(f7091,plain,(
% 12.55/2.01    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_78 | ~spl6_93 | ~spl6_104)),
% 12.55/2.01    inference(subsumption_resolution,[],[f7090,f909])).
% 12.55/2.01  fof(f909,plain,(
% 12.55/2.01    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_78),
% 12.55/2.01    inference(avatar_component_clause,[],[f907])).
% 12.55/2.01  fof(f7090,plain,(
% 12.55/2.01    ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_93 | ~spl6_104)),
% 12.55/2.01    inference(subsumption_resolution,[],[f7089,f207])).
% 12.55/2.01  fof(f7089,plain,(
% 12.55/2.01    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_13 | ~spl6_93 | ~spl6_104)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5856,f212])).
% 12.55/2.01  fof(f5856,plain,(
% 12.55/2.01    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_93 | ~spl6_104)),
% 12.55/2.01    inference(resolution,[],[f1180,f1089])).
% 12.55/2.01  fof(f1089,plain,(
% 12.55/2.01    ( ! [X2,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~v5_pre_topc(k1_xboole_0,X1,X2) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)) ) | ~spl6_93),
% 12.55/2.01    inference(avatar_component_clause,[],[f1088])).
% 12.55/2.01  fof(f7084,plain,(
% 12.55/2.01    sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != u1_struct_0(sK1) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(theory_tautology_sat_conflict,[])).
% 12.55/2.01  fof(f7080,plain,(
% 12.55/2.01    sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 12.55/2.01    introduced(theory_tautology_sat_conflict,[])).
% 12.55/2.01  fof(f6915,plain,(
% 12.55/2.01    sK2 != sK3 | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.01    introduced(theory_tautology_sat_conflict,[])).
% 12.55/2.01  fof(f6904,plain,(
% 12.55/2.01    ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_92 | spl6_95 | ~spl6_97 | ~spl6_152 | ~spl6_322),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f6903])).
% 12.55/2.01  fof(f6903,plain,(
% 12.55/2.01    $false | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_92 | spl6_95 | ~spl6_97 | ~spl6_152 | ~spl6_322)),
% 12.55/2.01    inference(subsumption_resolution,[],[f6902,f1114])).
% 12.55/2.01  fof(f1114,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl6_95),
% 12.55/2.01    inference(avatar_component_clause,[],[f1113])).
% 12.55/2.01  fof(f6902,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_92 | ~spl6_97 | ~spl6_152 | ~spl6_322)),
% 12.55/2.01    inference(subsumption_resolution,[],[f6901,f1948])).
% 12.55/2.01  fof(f1948,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl6_152),
% 12.55/2.01    inference(avatar_component_clause,[],[f1947])).
% 12.55/2.01  fof(f6901,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_92 | ~spl6_97 | ~spl6_322)),
% 12.55/2.01    inference(subsumption_resolution,[],[f6900,f1127])).
% 12.55/2.01  fof(f6900,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_92 | ~spl6_322)),
% 12.55/2.01    inference(subsumption_resolution,[],[f6899,f207])).
% 12.55/2.01  fof(f6899,plain,(
% 12.55/2.01    ~l1_pre_topc(sK0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_38 | ~spl6_92 | ~spl6_322)),
% 12.55/2.01    inference(subsumption_resolution,[],[f6890,f212])).
% 12.55/2.01  fof(f6890,plain,(
% 12.55/2.01    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_92 | ~spl6_322)),
% 12.55/2.01    inference(resolution,[],[f5832,f6064])).
% 12.55/2.01  fof(f6064,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~spl6_322),
% 12.55/2.01    inference(avatar_component_clause,[],[f6062])).
% 12.55/2.01  fof(f5832,plain,(
% 12.55/2.01    ( ! [X45] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45))),k1_xboole_0) | ~v2_pre_topc(X45) | ~l1_pre_topc(X45) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X45),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)),sK1) | v5_pre_topc(k1_xboole_0,X45,sK1)) ) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_92)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5831,f197])).
% 12.55/2.01  fof(f5831,plain,(
% 12.55/2.01    ( ! [X45] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45))),k1_xboole_0) | ~v2_pre_topc(X45) | ~l1_pre_topc(X45) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X45),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)),sK1) | v5_pre_topc(k1_xboole_0,X45,sK1)) ) | (~spl6_11 | ~spl6_38 | ~spl6_92)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5676,f202])).
% 12.55/2.01  fof(f5676,plain,(
% 12.55/2.01    ( ! [X45] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45))),k1_xboole_0) | ~v2_pre_topc(X45) | ~l1_pre_topc(X45) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X45),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)),sK1) | v5_pre_topc(k1_xboole_0,X45,sK1)) ) | (~spl6_38 | ~spl6_92)),
% 12.55/2.01    inference(superposition,[],[f1084,f476])).
% 12.55/2.01  fof(f1084,plain,(
% 12.55/2.01    ( ! [X2,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | v5_pre_topc(k1_xboole_0,X1,X2)) ) | ~spl6_92),
% 12.55/2.01    inference(avatar_component_clause,[],[f1083])).
% 12.55/2.01  fof(f1083,plain,(
% 12.55/2.01    spl6_92 <=> ! [X1,X2] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | v5_pre_topc(k1_xboole_0,X1,X2))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 12.55/2.01  fof(f6435,plain,(
% 12.55/2.01    ~spl6_31 | ~spl6_77 | ~spl6_85 | spl6_230),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f6431])).
% 12.55/2.01  fof(f6431,plain,(
% 12.55/2.01    $false | (~spl6_31 | ~spl6_77 | ~spl6_85 | spl6_230)),
% 12.55/2.01    inference(unit_resulting_resolution,[],[f903,f3361,f2752])).
% 12.55/2.01  fof(f2752,plain,(
% 12.55/2.01    ( ! [X2] : (k1_xboole_0 = X2 | ~v1_xboole_0(X2)) ) | (~spl6_31 | ~spl6_85)),
% 12.55/2.01    inference(resolution,[],[f1698,f1555])).
% 12.55/2.01  fof(f1555,plain,(
% 12.55/2.01    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | (~spl6_31 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f1554,f993])).
% 12.55/2.01  fof(f1554,plain,(
% 12.55/2.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,sK2)) ) | (~spl6_31 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f998,f993])).
% 12.55/2.01  fof(f998,plain,(
% 12.55/2.01    ( ! [X0] : (sK2 = X0 | ~r1_tarski(X0,sK2)) ) | ~spl6_31),
% 12.55/2.01    inference(resolution,[],[f995,f106])).
% 12.55/2.01  fof(f106,plain,(
% 12.55/2.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 12.55/2.01    inference(cnf_transformation,[],[f69])).
% 12.55/2.01  fof(f69,plain,(
% 12.55/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.55/2.01    inference(flattening,[],[f68])).
% 12.55/2.01  fof(f68,plain,(
% 12.55/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 12.55/2.01    inference(nnf_transformation,[],[f3])).
% 12.55/2.01  fof(f3,axiom,(
% 12.55/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.55/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 12.55/2.01  fof(f995,plain,(
% 12.55/2.01    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl6_31),
% 12.55/2.01    inference(resolution,[],[f390,f123])).
% 12.55/2.01  fof(f123,plain,(
% 12.55/2.01    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 12.55/2.01    inference(cnf_transformation,[],[f76])).
% 12.55/2.01  fof(f76,plain,(
% 12.55/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.55/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f74,f75])).
% 12.55/2.01  fof(f75,plain,(
% 12.55/2.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 12.55/2.01    introduced(choice_axiom,[])).
% 12.55/2.01  fof(f74,plain,(
% 12.55/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 12.55/2.01    inference(rectify,[],[f73])).
% 12.55/2.01  fof(f73,plain,(
% 12.55/2.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 12.55/2.01    inference(nnf_transformation,[],[f52])).
% 12.55/2.01  fof(f52,plain,(
% 12.55/2.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 12.55/2.01    inference(ennf_transformation,[],[f1])).
% 12.55/2.01  fof(f1,axiom,(
% 12.55/2.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 12.55/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 12.55/2.01  fof(f390,plain,(
% 12.55/2.01    ( ! [X7] : (~r2_hidden(X7,sK2)) ) | ~spl6_31),
% 12.55/2.01    inference(avatar_component_clause,[],[f389])).
% 12.55/2.01  fof(f389,plain,(
% 12.55/2.01    spl6_31 <=> ! [X7] : ~r2_hidden(X7,sK2)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 12.55/2.01  fof(f1698,plain,(
% 12.55/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 12.55/2.01    inference(resolution,[],[f287,f123])).
% 12.55/2.01  fof(f287,plain,(
% 12.55/2.01    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 12.55/2.01    inference(subsumption_resolution,[],[f285,f129])).
% 12.55/2.01  fof(f129,plain,(
% 12.55/2.01    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 12.55/2.01    inference(cnf_transformation,[],[f4])).
% 12.55/2.01  fof(f4,axiom,(
% 12.55/2.01    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 12.55/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 12.55/2.01  fof(f285,plain,(
% 12.55/2.01    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v1_xboole_0(k1_tarski(X0)) | ~v1_xboole_0(X1)) )),
% 12.55/2.01    inference(resolution,[],[f130,f117])).
% 12.55/2.01  fof(f117,plain,(
% 12.55/2.01    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 12.55/2.01    inference(cnf_transformation,[],[f49])).
% 12.55/2.01  fof(f49,plain,(
% 12.55/2.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 12.55/2.01    inference(ennf_transformation,[],[f9])).
% 12.55/2.01  fof(f9,axiom,(
% 12.55/2.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 12.55/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 12.55/2.01  fof(f130,plain,(
% 12.55/2.01    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 12.55/2.01    inference(cnf_transformation,[],[f55])).
% 12.55/2.01  fof(f55,plain,(
% 12.55/2.01    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 12.55/2.01    inference(ennf_transformation,[],[f8])).
% 12.55/2.01  fof(f8,axiom,(
% 12.55/2.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 12.55/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 12.55/2.01  fof(f3361,plain,(
% 12.55/2.01    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl6_230),
% 12.55/2.01    inference(avatar_component_clause,[],[f3360])).
% 12.55/2.01  fof(f903,plain,(
% 12.55/2.01    v1_xboole_0(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_77),
% 12.55/2.01    inference(avatar_component_clause,[],[f902])).
% 12.55/2.01  fof(f6065,plain,(
% 12.55/2.01    spl6_322 | ~spl6_38 | ~spl6_220),
% 12.55/2.01    inference(avatar_split_clause,[],[f6060,f3231,f474,f6062])).
% 12.55/2.01  fof(f6060,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_38 | ~spl6_220)),
% 12.55/2.01    inference(forward_demodulation,[],[f3232,f476])).
% 12.55/2.01  fof(f3232,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl6_220),
% 12.55/2.01    inference(avatar_component_clause,[],[f3231])).
% 12.55/2.01  fof(f6058,plain,(
% 12.55/2.01    spl6_321 | ~spl6_23 | ~spl6_103 | ~spl6_110),
% 12.55/2.01    inference(avatar_split_clause,[],[f6049,f1255,f1166,f281,f6055])).
% 12.55/2.01  fof(f281,plain,(
% 12.55/2.01    spl6_23 <=> v1_relat_1(k1_xboole_0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 12.55/2.01  fof(f6049,plain,(
% 12.55/2.01    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_23 | ~spl6_103 | ~spl6_110)),
% 12.55/2.01    inference(resolution,[],[f5949,f1257])).
% 12.55/2.01  fof(f1257,plain,(
% 12.55/2.01    v1_partfun1(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl6_110),
% 12.55/2.01    inference(avatar_component_clause,[],[f1255])).
% 12.55/2.01  fof(f5949,plain,(
% 12.55/2.01    ( ! [X0] : (~v1_partfun1(k1_xboole_0,X0) | k1_xboole_0 = X0) ) | (~spl6_23 | ~spl6_103)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5948,f283])).
% 12.55/2.01  fof(f283,plain,(
% 12.55/2.01    v1_relat_1(k1_xboole_0) | ~spl6_23),
% 12.55/2.01    inference(avatar_component_clause,[],[f281])).
% 12.55/2.01  fof(f5948,plain,(
% 12.55/2.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_103),
% 12.55/2.01    inference(subsumption_resolution,[],[f5939,f314])).
% 12.55/2.01  fof(f314,plain,(
% 12.55/2.01    ( ! [X1] : (v4_relat_1(k1_xboole_0,X1)) )),
% 12.55/2.01    inference(resolution,[],[f127,f118])).
% 12.55/2.01  fof(f5939,plain,(
% 12.55/2.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_partfun1(k1_xboole_0,X0) | ~v4_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_103),
% 12.55/2.01    inference(superposition,[],[f1168,f107])).
% 12.55/2.01  fof(f5893,plain,(
% 12.55/2.01    ~spl6_18 | spl6_284),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f5889])).
% 12.55/2.01  fof(f5889,plain,(
% 12.55/2.01    $false | (~spl6_18 | spl6_284)),
% 12.55/2.01    inference(unit_resulting_resolution,[],[f269,f1825,f125,f4764,f107])).
% 12.55/2.01  fof(f4764,plain,(
% 12.55/2.01    k1_xboole_0 != k1_relat_1(k6_partfun1(k1_xboole_0)) | spl6_284),
% 12.55/2.01    inference(avatar_component_clause,[],[f4763])).
% 12.55/2.01  fof(f4763,plain,(
% 12.55/2.01    spl6_284 <=> k1_xboole_0 = k1_relat_1(k6_partfun1(k1_xboole_0))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_284])])).
% 12.55/2.01  fof(f125,plain,(
% 12.55/2.01    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 12.55/2.01    inference(cnf_transformation,[],[f19])).
% 12.55/2.01  fof(f19,axiom,(
% 12.55/2.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 12.55/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 12.55/2.01  fof(f1825,plain,(
% 12.55/2.01    ( ! [X0] : (v4_relat_1(k6_partfun1(k1_xboole_0),X0)) ) | ~spl6_18),
% 12.55/2.01    inference(resolution,[],[f317,f243])).
% 12.55/2.01  fof(f243,plain,(
% 12.55/2.01    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl6_18),
% 12.55/2.01    inference(avatar_component_clause,[],[f241])).
% 12.55/2.01  fof(f241,plain,(
% 12.55/2.01    spl6_18 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 12.55/2.01  fof(f317,plain,(
% 12.55/2.01    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 12.55/2.01    inference(superposition,[],[f127,f140])).
% 12.55/2.01  fof(f269,plain,(
% 12.55/2.01    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 12.55/2.01    inference(resolution,[],[f128,f126])).
% 12.55/2.01  fof(f126,plain,(
% 12.55/2.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 12.55/2.01    inference(cnf_transformation,[],[f19])).
% 12.55/2.01  fof(f128,plain,(
% 12.55/2.01    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 12.55/2.01    inference(cnf_transformation,[],[f54])).
% 12.55/2.01  fof(f54,plain,(
% 12.55/2.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 12.55/2.01    inference(ennf_transformation,[],[f12])).
% 12.55/2.01  fof(f12,axiom,(
% 12.55/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 12.55/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 12.55/2.01  fof(f5484,plain,(
% 12.55/2.01    spl6_103 | ~spl6_14 | ~spl6_18 | ~spl6_31 | ~spl6_85 | ~spl6_284),
% 12.55/2.01    inference(avatar_split_clause,[],[f5483,f4763,f991,f389,f241,f215,f1166])).
% 12.55/2.01  fof(f215,plain,(
% 12.55/2.01    spl6_14 <=> v1_xboole_0(k1_xboole_0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 12.55/2.01  fof(f5483,plain,(
% 12.55/2.01    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl6_14 | ~spl6_18 | ~spl6_31 | ~spl6_85 | ~spl6_284)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4787,f217])).
% 12.55/2.01  fof(f217,plain,(
% 12.55/2.01    v1_xboole_0(k1_xboole_0) | ~spl6_14),
% 12.55/2.01    inference(avatar_component_clause,[],[f215])).
% 12.55/2.01  fof(f4787,plain,(
% 12.55/2.01    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0) | (~spl6_14 | ~spl6_18 | ~spl6_31 | ~spl6_85 | ~spl6_284)),
% 12.55/2.01    inference(superposition,[],[f4765,f4532])).
% 12.55/2.01  fof(f4532,plain,(
% 12.55/2.01    ( ! [X4] : (k1_xboole_0 = k6_partfun1(X4) | ~v1_xboole_0(X4)) ) | (~spl6_14 | ~spl6_18 | ~spl6_31 | ~spl6_85)),
% 12.55/2.01    inference(resolution,[],[f4301,f1555])).
% 12.55/2.01  fof(f4301,plain,(
% 12.55/2.01    ( ! [X0,X1] : (r1_tarski(k6_partfun1(X0),X1) | ~v1_xboole_0(X0)) ) | (~spl6_14 | ~spl6_18 | ~spl6_31 | ~spl6_85)),
% 12.55/2.01    inference(resolution,[],[f2780,f123])).
% 12.55/2.01  fof(f2780,plain,(
% 12.55/2.01    ( ! [X0,X1] : (~r2_hidden(X1,k6_partfun1(X0)) | ~v1_xboole_0(X0)) ) | (~spl6_14 | ~spl6_18 | ~spl6_31 | ~spl6_85)),
% 12.55/2.01    inference(superposition,[],[f600,f2752])).
% 12.55/2.01  fof(f600,plain,(
% 12.55/2.01    ( ! [X0] : (~r2_hidden(X0,k6_partfun1(k1_xboole_0))) ) | (~spl6_14 | ~spl6_18)),
% 12.55/2.01    inference(subsumption_resolution,[],[f597,f217])).
% 12.55/2.01  fof(f597,plain,(
% 12.55/2.01    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X0,k6_partfun1(k1_xboole_0))) ) | ~spl6_18),
% 12.55/2.01    inference(resolution,[],[f243,f112])).
% 12.55/2.01  fof(f112,plain,(
% 12.55/2.01    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 12.55/2.01    inference(cnf_transformation,[],[f45])).
% 12.55/2.01  fof(f45,plain,(
% 12.55/2.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 12.55/2.01    inference(ennf_transformation,[],[f11])).
% 12.55/2.01  fof(f11,axiom,(
% 12.55/2.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 12.55/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 12.55/2.01  fof(f4765,plain,(
% 12.55/2.01    k1_xboole_0 = k1_relat_1(k6_partfun1(k1_xboole_0)) | ~spl6_284),
% 12.55/2.01    inference(avatar_component_clause,[],[f4763])).
% 12.55/2.01  fof(f5451,plain,(
% 12.55/2.01    spl6_104 | ~spl6_76 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f5450,f991,f897,f1178])).
% 12.55/2.01  fof(f897,plain,(
% 12.55/2.01    spl6_76 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 12.55/2.01  fof(f5450,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_76 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f899,f993])).
% 12.55/2.01  fof(f899,plain,(
% 12.55/2.01    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_76),
% 12.55/2.01    inference(avatar_component_clause,[],[f897])).
% 12.55/2.01  fof(f5444,plain,(
% 12.55/2.01    spl6_152 | ~spl6_46 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f5443,f991,f529,f1947])).
% 12.55/2.01  fof(f5443,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_46 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f531,f993])).
% 12.55/2.01  fof(f531,plain,(
% 12.55/2.01    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl6_46),
% 12.55/2.01    inference(avatar_component_clause,[],[f529])).
% 12.55/2.01  fof(f5442,plain,(
% 12.55/2.01    spl6_219 | ~spl6_15 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f5441,f991,f222,f3223])).
% 12.55/2.01  fof(f5441,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_15 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f224,f993])).
% 12.55/2.01  fof(f224,plain,(
% 12.55/2.01    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_15),
% 12.55/2.01    inference(avatar_component_clause,[],[f222])).
% 12.55/2.01  fof(f5440,plain,(
% 12.55/2.01    spl6_219 | ~spl6_2 | ~spl6_96),
% 12.55/2.01    inference(avatar_split_clause,[],[f5439,f1118,f154,f3223])).
% 12.55/2.01  fof(f5439,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_96)),
% 12.55/2.01    inference(forward_demodulation,[],[f155,f1120])).
% 12.55/2.01  fof(f5432,plain,(
% 12.55/2.01    ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_84 | ~spl6_92 | spl6_95 | ~spl6_194 | ~spl6_217 | ~spl6_257),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f5431])).
% 12.55/2.01  fof(f5431,plain,(
% 12.55/2.01    $false | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_84 | ~spl6_92 | spl6_95 | ~spl6_194 | ~spl6_217 | ~spl6_257)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5430,f1114])).
% 12.55/2.01  fof(f5430,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_84 | ~spl6_92 | ~spl6_194 | ~spl6_217 | ~spl6_257)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5429,f202])).
% 12.55/2.01  fof(f5429,plain,(
% 12.55/2.01    ~v2_pre_topc(sK1) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_84 | ~spl6_92 | ~spl6_194 | ~spl6_217 | ~spl6_257)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5426,f197])).
% 12.55/2.01  fof(f5426,plain,(
% 12.55/2.01    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_12 | ~spl6_13 | ~spl6_84 | ~spl6_92 | ~spl6_194 | ~spl6_217 | ~spl6_257)),
% 12.55/2.01    inference(resolution,[],[f2902,f5258])).
% 12.55/2.01  fof(f5258,plain,(
% 12.55/2.01    ( ! [X44] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44) | ~l1_pre_topc(X44) | ~v2_pre_topc(X44) | v5_pre_topc(k1_xboole_0,sK0,X44)) ) | (~spl6_12 | ~spl6_13 | ~spl6_84 | ~spl6_92 | ~spl6_217 | ~spl6_257)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5257,f3098])).
% 12.55/2.01  fof(f3098,plain,(
% 12.55/2.01    ( ! [X4] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X4)) ) | ~spl6_217),
% 12.55/2.01    inference(avatar_component_clause,[],[f3097])).
% 12.55/2.01  fof(f5257,plain,(
% 12.55/2.01    ( ! [X44] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X44)) | ~v2_pre_topc(X44) | ~l1_pre_topc(X44) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44) | v5_pre_topc(k1_xboole_0,sK0,X44)) ) | (~spl6_12 | ~spl6_13 | ~spl6_84 | ~spl6_92 | ~spl6_217 | ~spl6_257)),
% 12.55/2.01    inference(forward_demodulation,[],[f5256,f3881])).
% 12.55/2.01  fof(f3881,plain,(
% 12.55/2.01    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~spl6_257),
% 12.55/2.01    inference(avatar_component_clause,[],[f3880])).
% 12.55/2.01  fof(f3880,plain,(
% 12.55/2.01    spl6_257 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_257])])).
% 12.55/2.01  fof(f5256,plain,(
% 12.55/2.01    ( ! [X44] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X44)) | ~v2_pre_topc(X44) | ~l1_pre_topc(X44) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44) | v5_pre_topc(k1_xboole_0,sK0,X44)) ) | (~spl6_12 | ~spl6_13 | ~spl6_84 | ~spl6_92 | ~spl6_217)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3686,f3098])).
% 12.55/2.01  fof(f3686,plain,(
% 12.55/2.01    ( ! [X44] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X44)) | ~v2_pre_topc(X44) | ~l1_pre_topc(X44) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X44)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44) | v5_pre_topc(k1_xboole_0,sK0,X44)) ) | (~spl6_12 | ~spl6_13 | ~spl6_84 | ~spl6_92)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3685,f207])).
% 12.55/2.01  fof(f3685,plain,(
% 12.55/2.01    ( ! [X44] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X44)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X44) | ~l1_pre_topc(X44) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X44)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44) | v5_pre_topc(k1_xboole_0,sK0,X44)) ) | (~spl6_13 | ~spl6_84 | ~spl6_92)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3551,f212])).
% 12.55/2.01  fof(f3551,plain,(
% 12.55/2.01    ( ! [X44] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X44)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X44) | ~l1_pre_topc(X44) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X44)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X44) | v5_pre_topc(k1_xboole_0,sK0,X44)) ) | (~spl6_84 | ~spl6_92)),
% 12.55/2.01    inference(superposition,[],[f1084,f989])).
% 12.55/2.01  fof(f989,plain,(
% 12.55/2.01    k1_xboole_0 = u1_struct_0(sK0) | ~spl6_84),
% 12.55/2.01    inference(avatar_component_clause,[],[f987])).
% 12.55/2.01  fof(f987,plain,(
% 12.55/2.01    spl6_84 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 12.55/2.01  fof(f2902,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | ~spl6_194),
% 12.55/2.01    inference(avatar_component_clause,[],[f2901])).
% 12.55/2.01  fof(f2901,plain,(
% 12.55/2.01    spl6_194 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_194])])).
% 12.55/2.01  fof(f5401,plain,(
% 12.55/2.01    ~spl6_95 | spl6_1 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f5400,f991,f150,f1113])).
% 12.55/2.01  fof(f5400,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (spl6_1 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f152,f993])).
% 12.55/2.01  fof(f152,plain,(
% 12.55/2.01    ~v5_pre_topc(sK2,sK0,sK1) | spl6_1),
% 12.55/2.01    inference(avatar_component_clause,[],[f150])).
% 12.55/2.01  fof(f5399,plain,(
% 12.55/2.01    spl6_227 | ~spl6_2 | ~spl6_84 | ~spl6_96),
% 12.55/2.01    inference(avatar_split_clause,[],[f5398,f1118,f987,f154,f3319])).
% 12.55/2.01  fof(f3319,plain,(
% 12.55/2.01    spl6_227 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_227])])).
% 12.55/2.01  fof(f5398,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_84 | ~spl6_96)),
% 12.55/2.01    inference(forward_demodulation,[],[f5397,f1120])).
% 12.55/2.01  fof(f5397,plain,(
% 12.55/2.01    v5_pre_topc(sK3,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_84)),
% 12.55/2.01    inference(forward_demodulation,[],[f155,f989])).
% 12.55/2.01  fof(f5378,plain,(
% 12.55/2.01    spl6_194 | ~spl6_227 | ~spl6_10 | ~spl6_11 | ~spl6_90 | ~spl6_94 | ~spl6_109 | ~spl6_217 | ~spl6_228 | ~spl6_257),
% 12.55/2.01    inference(avatar_split_clause,[],[f5377,f3880,f3323,f3097,f1236,f1093,f1038,f200,f195,f3319,f2901])).
% 12.55/2.01  fof(f1038,plain,(
% 12.55/2.01    spl6_90 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 12.55/2.01  fof(f1093,plain,(
% 12.55/2.01    spl6_94 <=> ! [X1,X2] : (~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | v5_pre_topc(k1_xboole_0,X1,X2))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 12.55/2.01  fof(f1236,plain,(
% 12.55/2.01    spl6_109 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).
% 12.55/2.01  fof(f5377,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_90 | ~spl6_94 | ~spl6_109 | ~spl6_217 | ~spl6_228 | ~spl6_257)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5376,f3098])).
% 12.55/2.01  fof(f5376,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_90 | ~spl6_94 | ~spl6_109 | ~spl6_228 | ~spl6_257)),
% 12.55/2.01    inference(forward_demodulation,[],[f5375,f3881])).
% 12.55/2.01  fof(f5375,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_90 | ~spl6_94 | ~spl6_109 | ~spl6_228)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5374,f197])).
% 12.55/2.01  fof(f5374,plain,(
% 12.55/2.01    ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl6_11 | ~spl6_90 | ~spl6_94 | ~spl6_109 | ~spl6_228)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5373,f202])).
% 12.55/2.01  fof(f5373,plain,(
% 12.55/2.01    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl6_90 | ~spl6_94 | ~spl6_109 | ~spl6_228)),
% 12.55/2.01    inference(subsumption_resolution,[],[f5372,f1237])).
% 12.55/2.01  fof(f1237,plain,(
% 12.55/2.01    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~spl6_109),
% 12.55/2.01    inference(avatar_component_clause,[],[f1236])).
% 12.55/2.01  fof(f5372,plain,(
% 12.55/2.01    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl6_90 | ~spl6_94 | ~spl6_228)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4809,f1040])).
% 12.55/2.01  fof(f1040,plain,(
% 12.55/2.01    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~spl6_90),
% 12.55/2.01    inference(avatar_component_clause,[],[f1038])).
% 12.55/2.01  fof(f4809,plain,(
% 12.55/2.01    ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),sK1) | (~spl6_94 | ~spl6_228)),
% 12.55/2.01    inference(resolution,[],[f3324,f1094])).
% 12.55/2.01  fof(f1094,plain,(
% 12.55/2.01    ( ! [X2,X1] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | v5_pre_topc(k1_xboole_0,X1,X2)) ) | ~spl6_94),
% 12.55/2.01    inference(avatar_component_clause,[],[f1093])).
% 12.55/2.01  fof(f3324,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_228),
% 12.55/2.01    inference(avatar_component_clause,[],[f3323])).
% 12.55/2.01  fof(f4859,plain,(
% 12.55/2.01    spl6_257 | ~spl6_103 | ~spl6_232),
% 12.55/2.01    inference(avatar_split_clause,[],[f4858,f3393,f1166,f3880])).
% 12.55/2.01  fof(f4858,plain,(
% 12.55/2.01    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl6_103 | ~spl6_232)),
% 12.55/2.01    inference(forward_demodulation,[],[f4857,f1168])).
% 12.55/2.01  fof(f4857,plain,(
% 12.55/2.01    k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~spl6_232),
% 12.55/2.01    inference(subsumption_resolution,[],[f4852,f118])).
% 12.55/2.01  fof(f4852,plain,(
% 12.55/2.01    k1_relat_1(k1_xboole_0) = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_232),
% 12.55/2.01    inference(superposition,[],[f100,f3395])).
% 12.55/2.01  fof(f3395,plain,(
% 12.55/2.01    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0) | ~spl6_232),
% 12.55/2.01    inference(avatar_component_clause,[],[f3393])).
% 12.55/2.01  fof(f4614,plain,(
% 12.55/2.01    ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_41 | ~spl6_84 | ~spl6_95 | ~spl6_217 | spl6_223),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f4613])).
% 12.55/2.01  fof(f4613,plain,(
% 12.55/2.01    $false | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_41 | ~spl6_84 | ~spl6_95 | ~spl6_217 | spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4612,f3098])).
% 12.55/2.01  fof(f4612,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_41 | ~spl6_84 | ~spl6_95 | ~spl6_217 | spl6_223)),
% 12.55/2.01    inference(forward_demodulation,[],[f4611,f989])).
% 12.55/2.01  fof(f4611,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_41 | ~spl6_84 | ~spl6_95 | ~spl6_217 | spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4610,f3098])).
% 12.55/2.01  fof(f4610,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_41 | ~spl6_84 | ~spl6_95 | spl6_223)),
% 12.55/2.01    inference(forward_demodulation,[],[f4609,f989])).
% 12.55/2.01  fof(f4609,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_41 | ~spl6_95 | spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4608,f1115])).
% 12.55/2.01  fof(f4608,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_41 | spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4607,f207])).
% 12.55/2.01  fof(f4607,plain,(
% 12.55/2.01    ~l1_pre_topc(sK0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_40 | ~spl6_41 | spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4605,f212])).
% 12.55/2.01  fof(f4605,plain,(
% 12.55/2.01    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_40 | ~spl6_41 | spl6_223)),
% 12.55/2.01    inference(resolution,[],[f3266,f4042])).
% 12.55/2.01  fof(f4042,plain,(
% 12.55/2.01    ( ! [X11] : (v5_pre_topc(k1_xboole_0,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X11),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,X11,sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X11),k1_xboole_0)) ) | (~spl6_10 | ~spl6_11 | ~spl6_40 | ~spl6_41)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4041,f197])).
% 12.55/2.01  fof(f4041,plain,(
% 12.55/2.01    ( ! [X11] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X11),k1_xboole_0) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X11),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,X11,sK1) | v5_pre_topc(k1_xboole_0,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | (~spl6_11 | ~spl6_40 | ~spl6_41)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3958,f202])).
% 12.55/2.01  fof(f3958,plain,(
% 12.55/2.01    ( ! [X11] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X11),k1_xboole_0) | ~v2_pre_topc(X11) | ~l1_pre_topc(X11) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X11),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,X11,sK1) | v5_pre_topc(k1_xboole_0,X11,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | (~spl6_40 | ~spl6_41)),
% 12.55/2.01    inference(superposition,[],[f500,f486])).
% 12.55/2.01  fof(f3266,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_223),
% 12.55/2.01    inference(avatar_component_clause,[],[f3265])).
% 12.55/2.01  fof(f3265,plain,(
% 12.55/2.01    spl6_223 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_223])])).
% 12.55/2.01  fof(f4573,plain,(
% 12.55/2.01    ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_84 | ~spl6_94 | spl6_95 | ~spl6_217 | ~spl6_223),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f4572])).
% 12.55/2.01  fof(f4572,plain,(
% 12.55/2.01    $false | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_84 | ~spl6_94 | spl6_95 | ~spl6_217 | ~spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4571,f3098])).
% 12.55/2.01  fof(f4571,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_84 | ~spl6_94 | spl6_95 | ~spl6_217 | ~spl6_223)),
% 12.55/2.01    inference(forward_demodulation,[],[f4570,f989])).
% 12.55/2.01  fof(f4570,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_84 | ~spl6_94 | spl6_95 | ~spl6_217 | ~spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4569,f3098])).
% 12.55/2.01  fof(f4569,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_84 | ~spl6_94 | spl6_95 | ~spl6_223)),
% 12.55/2.01    inference(forward_demodulation,[],[f4568,f989])).
% 12.55/2.01  fof(f4568,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_94 | spl6_95 | ~spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4567,f1114])).
% 12.55/2.01  fof(f4567,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_40 | ~spl6_94 | ~spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4566,f207])).
% 12.55/2.01  fof(f4566,plain,(
% 12.55/2.01    ~l1_pre_topc(sK0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_40 | ~spl6_94 | ~spl6_223)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4559,f212])).
% 12.55/2.01  fof(f4559,plain,(
% 12.55/2.01    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_40 | ~spl6_94 | ~spl6_223)),
% 12.55/2.01    inference(resolution,[],[f4083,f3267])).
% 12.55/2.01  fof(f3267,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_223),
% 12.55/2.01    inference(avatar_component_clause,[],[f3265])).
% 12.55/2.01  fof(f4083,plain,(
% 12.55/2.01    ( ! [X23] : (~v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(X23) | ~l1_pre_topc(X23) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0) | v5_pre_topc(k1_xboole_0,X23,sK1)) ) | (~spl6_10 | ~spl6_11 | ~spl6_40 | ~spl6_94)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4082,f197])).
% 12.55/2.01  fof(f4082,plain,(
% 12.55/2.01    ( ! [X23] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0) | ~v2_pre_topc(X23) | ~l1_pre_topc(X23) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X23,sK1)) ) | (~spl6_11 | ~spl6_40 | ~spl6_94)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3967,f202])).
% 12.55/2.01  fof(f3967,plain,(
% 12.55/2.01    ( ! [X23] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X23),k1_xboole_0) | ~v2_pre_topc(X23) | ~l1_pre_topc(X23) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X23),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,X23,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X23,sK1)) ) | (~spl6_40 | ~spl6_94)),
% 12.55/2.01    inference(superposition,[],[f1094,f486])).
% 12.55/2.01  fof(f4337,plain,(
% 12.55/2.01    ~spl6_103 | spl6_136 | ~spl6_217),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f4336])).
% 12.55/2.01  fof(f4336,plain,(
% 12.55/2.01    $false | (~spl6_103 | spl6_136 | ~spl6_217)),
% 12.55/2.01    inference(subsumption_resolution,[],[f4335,f3098])).
% 12.55/2.01  fof(f4335,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_103 | spl6_136)),
% 12.55/2.01    inference(forward_demodulation,[],[f1759,f1168])).
% 12.55/2.01  fof(f1759,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | spl6_136),
% 12.55/2.01    inference(avatar_component_clause,[],[f1758])).
% 12.55/2.01  fof(f1758,plain,(
% 12.55/2.01    spl6_136 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).
% 12.55/2.01  fof(f3764,plain,(
% 12.55/2.01    ~spl6_84 | ~spl6_217 | spl6_225),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f3763])).
% 12.55/2.01  fof(f3763,plain,(
% 12.55/2.01    $false | (~spl6_84 | ~spl6_217 | spl6_225)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3762,f3098])).
% 12.55/2.01  fof(f3762,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_84 | spl6_225)),
% 12.55/2.01    inference(forward_demodulation,[],[f3275,f989])).
% 12.55/2.01  fof(f3275,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl6_225),
% 12.55/2.01    inference(avatar_component_clause,[],[f3273])).
% 12.55/2.01  fof(f3273,plain,(
% 12.55/2.01    spl6_225 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_225])])).
% 12.55/2.01  fof(f3761,plain,(
% 12.55/2.01    ~spl6_10 | spl6_48),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f3760])).
% 12.55/2.01  fof(f3760,plain,(
% 12.55/2.01    $false | (~spl6_10 | spl6_48)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3758,f197])).
% 12.55/2.01  fof(f3758,plain,(
% 12.55/2.01    ~l1_pre_topc(sK1) | spl6_48),
% 12.55/2.01    inference(resolution,[],[f563,f292])).
% 12.55/2.01  fof(f563,plain,(
% 12.55/2.01    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_48),
% 12.55/2.01    inference(avatar_component_clause,[],[f561])).
% 12.55/2.01  fof(f561,plain,(
% 12.55/2.01    spl6_48 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 12.55/2.01  fof(f3563,plain,(
% 12.55/2.01    spl6_91 | ~spl6_12 | ~spl6_84),
% 12.55/2.01    inference(avatar_split_clause,[],[f3562,f987,f205,f1044])).
% 12.55/2.01  fof(f1044,plain,(
% 12.55/2.01    spl6_91 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 12.55/2.01  fof(f3562,plain,(
% 12.55/2.01    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl6_12 | ~spl6_84)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3520,f207])).
% 12.55/2.01  fof(f3520,plain,(
% 12.55/2.01    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~l1_pre_topc(sK0) | ~spl6_84),
% 12.55/2.01    inference(superposition,[],[f111,f989])).
% 12.55/2.01  fof(f3468,plain,(
% 12.55/2.01    spl6_84 | ~spl6_52 | ~spl6_85 | ~spl6_103),
% 12.55/2.01    inference(avatar_split_clause,[],[f3414,f1166,f991,f590,f987])).
% 12.55/2.01  fof(f3414,plain,(
% 12.55/2.01    k1_xboole_0 = u1_struct_0(sK0) | (~spl6_52 | ~spl6_85 | ~spl6_103)),
% 12.55/2.01    inference(forward_demodulation,[],[f3413,f1168])).
% 12.55/2.01  fof(f3413,plain,(
% 12.55/2.01    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | (~spl6_52 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f592,f993])).
% 12.55/2.01  fof(f3420,plain,(
% 12.55/2.01    sK2 != sK3 | k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | u1_struct_0(sK0) != k1_relat_1(sK2) | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.01    introduced(theory_tautology_sat_conflict,[])).
% 12.55/2.01  fof(f3399,plain,(
% 12.55/2.01    spl6_70 | ~spl6_85),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f3398])).
% 12.55/2.01  fof(f3398,plain,(
% 12.55/2.01    $false | (spl6_70 | ~spl6_85)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3397,f118])).
% 12.55/2.01  fof(f3397,plain,(
% 12.55/2.01    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (spl6_70 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f745,f993])).
% 12.55/2.01  fof(f745,plain,(
% 12.55/2.01    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl6_70),
% 12.55/2.01    inference(avatar_component_clause,[],[f743])).
% 12.55/2.01  fof(f3290,plain,(
% 12.55/2.01    spl6_224 | ~spl6_16 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f3289,f991,f228,f3269])).
% 12.55/2.01  fof(f3269,plain,(
% 12.55/2.01    spl6_224 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_224])])).
% 12.55/2.01  fof(f3289,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_16 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f230,f993])).
% 12.55/2.01  fof(f3285,plain,(
% 12.55/2.01    ~spl6_47 | ~spl6_48 | ~spl6_223 | spl6_219 | ~spl6_224 | ~spl6_225 | ~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f3284,f991,f453,f234,f210,f205,f3273,f3269,f3223,f3265,f561,f557])).
% 12.55/2.01  fof(f557,plain,(
% 12.55/2.01    spl6_47 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 12.55/2.01  fof(f453,plain,(
% 12.55/2.01    spl6_35 <=> v1_funct_1(k1_xboole_0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 12.55/2.01  fof(f3284,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3283,f993])).
% 12.55/2.01  fof(f3283,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3282,f118])).
% 12.55/2.01  fof(f3282,plain,(
% 12.55/2.01    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3281,f993])).
% 12.55/2.01  fof(f3281,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3280,f454])).
% 12.55/2.01  fof(f454,plain,(
% 12.55/2.01    v1_funct_1(k1_xboole_0) | ~spl6_35),
% 12.55/2.01    inference(avatar_component_clause,[],[f453])).
% 12.55/2.01  fof(f3280,plain,(
% 12.55/2.01    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3279,f993])).
% 12.55/2.01  fof(f3279,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3278,f993])).
% 12.55/2.01  fof(f3278,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3277,f993])).
% 12.55/2.01  fof(f3277,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f1268,f993])).
% 12.55/2.01  fof(f1268,plain,(
% 12.55/2.01    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17)),
% 12.55/2.01    inference(subsumption_resolution,[],[f1267,f212])).
% 12.55/2.01  fof(f1267,plain,(
% 12.55/2.01    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_12 | ~spl6_17)),
% 12.55/2.01    inference(subsumption_resolution,[],[f534,f207])).
% 12.55/2.01  fof(f534,plain,(
% 12.55/2.01    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl6_17),
% 12.55/2.01    inference(resolution,[],[f147,f236])).
% 12.55/2.01  fof(f3276,plain,(
% 12.55/2.01    ~spl6_47 | ~spl6_48 | ~spl6_219 | spl6_223 | ~spl6_224 | ~spl6_225 | ~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f3263,f991,f453,f234,f210,f205,f3273,f3269,f3265,f3223,f561,f557])).
% 12.55/2.01  fof(f3263,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3262,f993])).
% 12.55/2.01  fof(f3262,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3261,f118])).
% 12.55/2.01  fof(f3261,plain,(
% 12.55/2.01    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3260,f993])).
% 12.55/2.01  fof(f3260,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_35 | ~spl6_85)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3259,f454])).
% 12.55/2.01  fof(f3259,plain,(
% 12.55/2.01    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3258,f993])).
% 12.55/2.01  fof(f3258,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3257,f993])).
% 12.55/2.01  fof(f3257,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3256,f993])).
% 12.55/2.01  fof(f3256,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f1274,f993])).
% 12.55/2.01  fof(f1274,plain,(
% 12.55/2.01    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_12 | ~spl6_13 | ~spl6_17)),
% 12.55/2.01    inference(subsumption_resolution,[],[f1273,f212])).
% 12.55/2.01  fof(f1273,plain,(
% 12.55/2.01    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl6_12 | ~spl6_17)),
% 12.55/2.01    inference(subsumption_resolution,[],[f546,f207])).
% 12.55/2.01  fof(f546,plain,(
% 12.55/2.01    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl6_17),
% 12.55/2.01    inference(resolution,[],[f148,f236])).
% 12.55/2.01  fof(f3197,plain,(
% 12.55/2.01    u1_struct_0(sK0) != k1_relat_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | ~v1_partfun1(sK2,k1_relat_1(sK2))),
% 12.55/2.01    introduced(theory_tautology_sat_conflict,[])).
% 12.55/2.01  fof(f3189,plain,(
% 12.55/2.01    ~spl6_103 | spl6_106),
% 12.55/2.01    inference(avatar_contradiction_clause,[],[f3181])).
% 12.55/2.01  fof(f3181,plain,(
% 12.55/2.01    $false | (~spl6_103 | spl6_106)),
% 12.55/2.01    inference(unit_resulting_resolution,[],[f1195,f118,f1168,f418])).
% 12.55/2.01  fof(f1195,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl6_106),
% 12.55/2.01    inference(avatar_component_clause,[],[f1193])).
% 12.55/2.01  fof(f1193,plain,(
% 12.55/2.01    spl6_106 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).
% 12.55/2.01  fof(f3152,plain,(
% 12.55/2.01    spl6_100 | ~spl6_15 | ~spl6_38 | ~spl6_85),
% 12.55/2.01    inference(avatar_split_clause,[],[f3151,f991,f474,f222,f1143])).
% 12.55/2.01  fof(f3151,plain,(
% 12.55/2.01    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_15 | ~spl6_38 | ~spl6_85)),
% 12.55/2.01    inference(forward_demodulation,[],[f3150,f993])).
% 12.55/2.01  fof(f3150,plain,(
% 12.55/2.01    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_15 | ~spl6_38)),
% 12.55/2.01    inference(forward_demodulation,[],[f224,f476])).
% 12.55/2.01  fof(f3146,plain,(
% 12.55/2.01    ~spl6_98 | ~spl6_38 | spl6_44 | ~spl6_85 | ~spl6_133),
% 12.55/2.01    inference(avatar_split_clause,[],[f3145,f1718,f991,f521,f474,f1130])).
% 12.55/2.01  fof(f1130,plain,(
% 12.55/2.01    spl6_98 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 12.55/2.01  fof(f3145,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_38 | spl6_44 | ~spl6_85 | ~spl6_133)),
% 12.55/2.01    inference(forward_demodulation,[],[f3144,f993])).
% 12.55/2.01  fof(f3144,plain,(
% 12.55/2.01    ~v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_38 | spl6_44 | ~spl6_133)),
% 12.55/2.01    inference(forward_demodulation,[],[f3143,f1720])).
% 12.55/2.01  fof(f1720,plain,(
% 12.55/2.01    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~spl6_133),
% 12.55/2.01    inference(avatar_component_clause,[],[f1718])).
% 12.55/2.01  fof(f3143,plain,(
% 12.55/2.01    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_38 | spl6_44)),
% 12.55/2.01    inference(forward_demodulation,[],[f523,f476])).
% 12.55/2.01  fof(f523,plain,(
% 12.55/2.01    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl6_44),
% 12.55/2.01    inference(avatar_component_clause,[],[f521])).
% 12.55/2.01  fof(f3127,plain,(
% 12.55/2.01    ~spl6_100 | ~spl6_98 | ~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_42 | ~spl6_43 | ~spl6_94 | ~spl6_133 | ~spl6_136 | spl6_152),
% 12.55/2.01    inference(avatar_split_clause,[],[f3126,f1947,f1758,f1718,f1093,f517,f513,f474,f200,f195,f1130,f1143])).
% 12.55/2.01  fof(f517,plain,(
% 12.55/2.01    spl6_43 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 12.55/2.01    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 12.55/2.01  fof(f3126,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_42 | ~spl6_43 | ~spl6_94 | ~spl6_133 | ~spl6_136 | spl6_152)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3125,f1949])).
% 12.55/2.01  fof(f1949,plain,(
% 12.55/2.01    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl6_152),
% 12.55/2.01    inference(avatar_component_clause,[],[f1947])).
% 12.55/2.01  fof(f3125,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_42 | ~spl6_43 | ~spl6_94 | ~spl6_133 | ~spl6_136)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3124,f518])).
% 12.55/2.01  fof(f518,plain,(
% 12.55/2.01    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_43),
% 12.55/2.01    inference(avatar_component_clause,[],[f517])).
% 12.55/2.01  fof(f3124,plain,(
% 12.55/2.01    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_42 | ~spl6_94 | ~spl6_133 | ~spl6_136)),
% 12.55/2.01    inference(subsumption_resolution,[],[f3123,f514])).
% 12.55/2.01  fof(f3123,plain,(
% 12.55/2.01    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_94 | ~spl6_133 | ~spl6_136)),
% 12.55/2.01    inference(subsumption_resolution,[],[f2996,f1760])).
% 12.55/2.01  fof(f1760,plain,(
% 12.55/2.01    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_136),
% 12.55/2.01    inference(avatar_component_clause,[],[f1758])).
% 12.55/2.01  fof(f2996,plain,(
% 12.55/2.01    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_94 | ~spl6_133)),
% 12.55/2.01    inference(superposition,[],[f2274,f1720])).
% 12.55/2.01  fof(f2274,plain,(
% 12.55/2.01    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_94)),
% 12.55/2.01    inference(subsumption_resolution,[],[f2273,f197])).
% 12.55/2.01  fof(f2273,plain,(
% 12.55/2.01    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl6_11 | ~spl6_38 | ~spl6_94)),
% 12.55/2.01    inference(subsumption_resolution,[],[f2263,f202])).
% 12.55/2.02  % (24938)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 12.55/2.02  fof(f2263,plain,(
% 12.55/2.02    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(X0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,X0,sK1)) ) | (~spl6_38 | ~spl6_94)),
% 12.55/2.02    inference(superposition,[],[f1094,f476])).
% 12.55/2.02  fof(f3122,plain,(
% 12.55/2.02    ~spl6_95 | ~spl6_98 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_93 | ~spl6_97 | ~spl6_133 | spl6_152),
% 12.55/2.02    inference(avatar_split_clause,[],[f3121,f1947,f1718,f1125,f1088,f474,f210,f205,f200,f195,f1130,f1113])).
% 12.55/2.02  fof(f3121,plain,(
% 12.55/2.02    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_93 | ~spl6_97 | ~spl6_133 | spl6_152)),
% 12.55/2.02    inference(subsumption_resolution,[],[f3089,f1949])).
% 12.55/2.02  fof(f3089,plain,(
% 12.55/2.02    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_93 | ~spl6_97 | ~spl6_133)),
% 12.55/2.02    inference(subsumption_resolution,[],[f3088,f1127])).
% 12.55/2.02  fof(f3088,plain,(
% 12.55/2.02    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_38 | ~spl6_93 | ~spl6_133)),
% 12.55/2.02    inference(subsumption_resolution,[],[f3087,f207])).
% 12.55/2.02  fof(f3087,plain,(
% 12.55/2.02    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(sK0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_38 | ~spl6_93 | ~spl6_133)),
% 12.55/2.02    inference(subsumption_resolution,[],[f3069,f212])).
% 12.55/2.02  fof(f3069,plain,(
% 12.55/2.02    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_93 | ~spl6_133)),
% 12.55/2.02    inference(superposition,[],[f2255,f1720])).
% 12.55/2.02  fof(f2255,plain,(
% 12.55/2.02    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)) ) | (~spl6_10 | ~spl6_11 | ~spl6_38 | ~spl6_93)),
% 12.55/2.02    inference(subsumption_resolution,[],[f2254,f197])).
% 12.55/2.02  fof(f2254,plain,(
% 12.55/2.02    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)) ) | (~spl6_11 | ~spl6_38 | ~spl6_93)),
% 12.55/2.02    inference(subsumption_resolution,[],[f2241,f202])).
% 12.55/2.02  fof(f2241,plain,(
% 12.55/2.02    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),k1_xboole_0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,X0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1)) ) | (~spl6_38 | ~spl6_93)),
% 12.55/2.02    inference(superposition,[],[f1089,f476])).
% 12.55/2.02  fof(f1944,plain,(
% 12.55/2.02    ~spl6_38 | spl6_45 | ~spl6_85),
% 12.55/2.02    inference(avatar_contradiction_clause,[],[f1943])).
% 12.55/2.02  fof(f1943,plain,(
% 12.55/2.02    $false | (~spl6_38 | spl6_45 | ~spl6_85)),
% 12.55/2.02    inference(subsumption_resolution,[],[f1942,f118])).
% 12.55/2.02  fof(f1942,plain,(
% 12.55/2.02    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl6_38 | spl6_45 | ~spl6_85)),
% 12.55/2.02    inference(forward_demodulation,[],[f1941,f993])).
% 12.55/2.02  fof(f1941,plain,(
% 12.55/2.02    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_38 | spl6_45)),
% 12.55/2.02    inference(forward_demodulation,[],[f1940,f140])).
% 12.55/2.02  fof(f1940,plain,(
% 12.55/2.02    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl6_38 | spl6_45)),
% 12.55/2.02    inference(forward_demodulation,[],[f527,f476])).
% 12.55/2.02  fof(f527,plain,(
% 12.55/2.02    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl6_45),
% 12.55/2.02    inference(avatar_component_clause,[],[f525])).
% 12.55/2.02  fof(f525,plain,(
% 12.55/2.02    spl6_45 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 12.55/2.02    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 12.55/2.02  fof(f1881,plain,(
% 12.55/2.02    ~spl6_12 | spl6_43),
% 12.55/2.02    inference(avatar_contradiction_clause,[],[f1880])).
% 12.55/2.02  fof(f1880,plain,(
% 12.55/2.02    $false | (~spl6_12 | spl6_43)),
% 12.55/2.02    inference(subsumption_resolution,[],[f1875,f207])).
% 12.55/2.02  fof(f1875,plain,(
% 12.55/2.02    ~l1_pre_topc(sK0) | spl6_43),
% 12.55/2.02    inference(resolution,[],[f292,f519])).
% 12.55/2.02  fof(f519,plain,(
% 12.55/2.02    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl6_43),
% 12.55/2.02    inference(avatar_component_clause,[],[f517])).
% 12.55/2.02  fof(f1723,plain,(
% 12.55/2.02    spl6_133 | ~spl6_132),
% 12.55/2.02    inference(avatar_split_clause,[],[f1722,f1703,f1718])).
% 12.55/2.02  fof(f1703,plain,(
% 12.55/2.02    spl6_132 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)),
% 12.55/2.02    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).
% 12.55/2.02  fof(f1722,plain,(
% 12.55/2.02    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~spl6_132),
% 12.55/2.02    inference(subsumption_resolution,[],[f1714,f118])).
% 12.55/2.02  fof(f1714,plain,(
% 12.55/2.02    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~spl6_132),
% 12.55/2.02    inference(superposition,[],[f100,f1705])).
% 12.55/2.02  fof(f1705,plain,(
% 12.55/2.02    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | ~spl6_132),
% 12.55/2.02    inference(avatar_component_clause,[],[f1703])).
% 12.55/2.02  fof(f1706,plain,(
% 12.55/2.02    spl6_132 | ~spl6_38 | ~spl6_39 | ~spl6_85),
% 12.55/2.02    inference(avatar_split_clause,[],[f1701,f991,f480,f474,f1703])).
% 12.55/2.02  fof(f480,plain,(
% 12.55/2.02    spl6_39 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 12.55/2.02    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 12.55/2.02  fof(f1701,plain,(
% 12.55/2.02    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | (~spl6_38 | ~spl6_39 | ~spl6_85)),
% 12.55/2.02    inference(forward_demodulation,[],[f1700,f476])).
% 12.55/2.02  fof(f1700,plain,(
% 12.55/2.02    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_xboole_0) | (~spl6_39 | ~spl6_85)),
% 12.55/2.02    inference(forward_demodulation,[],[f482,f993])).
% 12.55/2.02  fof(f482,plain,(
% 12.55/2.02    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl6_39),
% 12.55/2.02    inference(avatar_component_clause,[],[f480])).
% 12.55/2.02  fof(f1549,plain,(
% 12.55/2.02    spl6_109 | ~spl6_91),
% 12.55/2.02    inference(avatar_split_clause,[],[f1542,f1044,f1236])).
% 12.55/2.02  fof(f1542,plain,(
% 12.55/2.02    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~spl6_91),
% 12.55/2.02    inference(resolution,[],[f1046,f109])).
% 12.55/2.02  fof(f1046,plain,(
% 12.55/2.02    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~spl6_91),
% 12.55/2.02    inference(avatar_component_clause,[],[f1044])).
% 12.55/2.02  fof(f1408,plain,(
% 12.55/2.02    spl6_97 | ~spl6_74 | ~spl6_85),
% 12.55/2.02    inference(avatar_split_clause,[],[f1401,f991,f887,f1125])).
% 12.55/2.02  fof(f887,plain,(
% 12.55/2.02    spl6_74 <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)),
% 12.55/2.02    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 12.55/2.02  fof(f1401,plain,(
% 12.55/2.02    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_74 | ~spl6_85)),
% 12.55/2.02    inference(backward_demodulation,[],[f889,f993])).
% 12.55/2.02  fof(f889,plain,(
% 12.55/2.02    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl6_74),
% 12.55/2.02    inference(avatar_component_clause,[],[f887])).
% 12.55/2.02  fof(f1407,plain,(
% 12.55/2.02    spl6_35 | ~spl6_9 | ~spl6_85),
% 12.55/2.02    inference(avatar_split_clause,[],[f1396,f991,f190,f453])).
% 12.55/2.02  fof(f1396,plain,(
% 12.55/2.02    v1_funct_1(k1_xboole_0) | (~spl6_9 | ~spl6_85)),
% 12.55/2.02    inference(backward_demodulation,[],[f192,f993])).
% 12.55/2.02  fof(f1389,plain,(
% 12.55/2.02    ~spl6_24 | ~spl6_31 | spl6_85),
% 12.55/2.02    inference(avatar_contradiction_clause,[],[f1386])).
% 12.55/2.02  fof(f1386,plain,(
% 12.55/2.02    $false | (~spl6_24 | ~spl6_31 | spl6_85)),
% 12.55/2.02    inference(unit_resulting_resolution,[],[f308,f992,f995,f106])).
% 12.55/2.02  fof(f992,plain,(
% 12.55/2.02    k1_xboole_0 != sK2 | spl6_85),
% 12.55/2.02    inference(avatar_component_clause,[],[f991])).
% 12.55/2.02  fof(f308,plain,(
% 12.55/2.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_24),
% 12.55/2.02    inference(resolution,[],[f303,f123])).
% 12.55/2.02  fof(f303,plain,(
% 12.55/2.02    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl6_24),
% 12.55/2.02    inference(avatar_component_clause,[],[f302])).
% 12.55/2.02  fof(f302,plain,(
% 12.55/2.02    spl6_24 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 12.55/2.02    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 12.55/2.02  fof(f1375,plain,(
% 12.55/2.02    spl6_31 | ~spl6_14 | ~spl6_73),
% 12.55/2.02    inference(avatar_split_clause,[],[f1374,f882,f215,f389])).
% 12.55/2.02  fof(f1374,plain,(
% 12.55/2.02    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl6_14 | ~spl6_73)),
% 12.55/2.02    inference(subsumption_resolution,[],[f1371,f217])).
% 12.55/2.02  fof(f1371,plain,(
% 12.55/2.02    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X0,sK2)) ) | ~spl6_73),
% 12.55/2.02    inference(resolution,[],[f884,f112])).
% 12.55/2.02  fof(f884,plain,(
% 12.55/2.02    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_73),
% 12.55/2.02    inference(avatar_component_clause,[],[f882])).
% 12.55/2.02  fof(f1370,plain,(
% 12.55/2.02    spl6_79 | ~spl6_38 | ~spl6_48),
% 12.55/2.02    inference(avatar_split_clause,[],[f1306,f561,f474,f912])).
% 12.55/2.02  fof(f1306,plain,(
% 12.55/2.02    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_38 | ~spl6_48)),
% 12.55/2.02    inference(forward_demodulation,[],[f562,f476])).
% 12.55/2.02  fof(f562,plain,(
% 12.55/2.02    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_48),
% 12.55/2.02    inference(avatar_component_clause,[],[f561])).
% 12.55/2.02  fof(f1356,plain,(
% 12.55/2.02    ~spl6_101 | spl6_2 | ~spl6_38),
% 12.55/2.02    inference(avatar_split_clause,[],[f1355,f474,f154,f1149])).
% 12.55/2.02  fof(f1355,plain,(
% 12.55/2.02    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl6_2 | ~spl6_38)),
% 12.55/2.02    inference(forward_demodulation,[],[f156,f476])).
% 12.55/2.02  fof(f1342,plain,(
% 12.55/2.02    spl6_31 | ~spl6_7 | ~spl6_14 | ~spl6_38),
% 12.55/2.02    inference(avatar_split_clause,[],[f1228,f474,f215,f180,f389])).
% 12.55/2.02  fof(f1228,plain,(
% 12.55/2.02    ( ! [X7] : (~r2_hidden(X7,sK2)) ) | (~spl6_7 | ~spl6_14 | ~spl6_38)),
% 12.55/2.02    inference(subsumption_resolution,[],[f1227,f217])).
% 12.55/2.02  fof(f1227,plain,(
% 12.55/2.02    ( ! [X7] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X7,sK2)) ) | (~spl6_7 | ~spl6_38)),
% 12.55/2.02    inference(forward_demodulation,[],[f1226,f140])).
% 12.55/2.02  fof(f1226,plain,(
% 12.55/2.02    ( ! [X7] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)) | ~r2_hidden(X7,sK2)) ) | (~spl6_7 | ~spl6_38)),
% 12.55/2.02    inference(forward_demodulation,[],[f297,f476])).
% 12.55/2.02  fof(f297,plain,(
% 12.55/2.02    ( ! [X7] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~r2_hidden(X7,sK2)) ) | ~spl6_7),
% 12.55/2.02    inference(resolution,[],[f112,f182])).
% 12.55/2.02  fof(f1308,plain,(
% 12.55/2.02    sK2 != sK3 | k1_xboole_0 != sK3 | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 12.55/2.02    introduced(theory_tautology_sat_conflict,[])).
% 12.55/2.02  fof(f1196,plain,(
% 12.55/2.02    ~spl6_106 | spl6_98 | ~spl6_103),
% 12.55/2.02    inference(avatar_split_clause,[],[f1183,f1166,f1130,f1193])).
% 12.55/2.02  fof(f1183,plain,(
% 12.55/2.02    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl6_98 | ~spl6_103)),
% 12.55/2.02    inference(backward_demodulation,[],[f1132,f1168])).
% 12.55/2.02  fof(f1132,plain,(
% 12.55/2.02    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | spl6_98),
% 12.55/2.02    inference(avatar_component_clause,[],[f1130])).
% 12.55/2.02  fof(f1095,plain,(
% 12.55/2.02    ~spl6_35 | spl6_94),
% 12.55/2.02    inference(avatar_split_clause,[],[f1091,f1093,f453])).
% 12.55/2.02  fof(f1091,plain,(
% 12.55/2.02    ( ! [X2,X1] : (~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | v5_pre_topc(k1_xboole_0,X1,X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 12.55/2.02    inference(subsumption_resolution,[],[f504,f118])).
% 12.55/2.02  fof(f504,plain,(
% 12.55/2.02    ( ! [X2,X1] : (~v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | v5_pre_topc(k1_xboole_0,X1,X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 12.55/2.02    inference(resolution,[],[f146,f118])).
% 12.55/2.02  fof(f1090,plain,(
% 12.55/2.02    ~spl6_35 | spl6_93),
% 12.55/2.02    inference(avatar_split_clause,[],[f1086,f1088,f453])).
% 12.55/2.02  fof(f1086,plain,(
% 12.55/2.02    ( ! [X2,X1] : (~v5_pre_topc(k1_xboole_0,X1,X2) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 12.55/2.02    inference(subsumption_resolution,[],[f536,f118])).
% 12.55/2.02  fof(f536,plain,(
% 12.55/2.02    ( ! [X2,X1] : (~v5_pre_topc(k1_xboole_0,X1,X2) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 12.55/2.02    inference(resolution,[],[f147,f118])).
% 12.55/2.02  fof(f1085,plain,(
% 12.55/2.02    ~spl6_35 | spl6_92),
% 12.55/2.02    inference(avatar_split_clause,[],[f1081,f1083,f453])).
% 12.55/2.02  fof(f1081,plain,(
% 12.55/2.02    ( ! [X2,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | v5_pre_topc(k1_xboole_0,X1,X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 12.55/2.02    inference(subsumption_resolution,[],[f548,f118])).
% 12.55/2.02  fof(f548,plain,(
% 12.55/2.02    ( ! [X2,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) | v5_pre_topc(k1_xboole_0,X1,X2) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 12.55/2.02    inference(resolution,[],[f148,f118])).
% 12.55/2.02  fof(f1041,plain,(
% 12.55/2.02    spl6_90 | ~spl6_12 | ~spl6_13 | ~spl6_84),
% 12.55/2.02    inference(avatar_split_clause,[],[f1036,f987,f210,f205,f1038])).
% 12.55/2.02  fof(f1036,plain,(
% 12.55/2.02    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl6_12 | ~spl6_13 | ~spl6_84)),
% 12.55/2.02    inference(subsumption_resolution,[],[f1035,f212])).
% 12.55/2.02  fof(f1035,plain,(
% 12.55/2.02    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | (~spl6_12 | ~spl6_84)),
% 12.55/2.02    inference(subsumption_resolution,[],[f1005,f207])).
% 12.55/2.02  fof(f1005,plain,(
% 12.55/2.02    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl6_84),
% 12.55/2.02    inference(superposition,[],[f110,f989])).
% 12.55/2.02  fof(f110,plain,(
% 12.55/2.02    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.55/2.02    inference(cnf_transformation,[],[f43])).
% 12.55/2.02  fof(f43,plain,(
% 12.55/2.02    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.55/2.02    inference(flattening,[],[f42])).
% 12.55/2.02  fof(f42,plain,(
% 12.55/2.02    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.55/2.02    inference(ennf_transformation,[],[f27])).
% 12.55/2.02  fof(f27,plain,(
% 12.55/2.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 12.55/2.02    inference(pure_predicate_removal,[],[f22])).
% 12.55/2.02  fof(f22,axiom,(
% 12.55/2.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 12.55/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 12.55/2.02  fof(f910,plain,(
% 12.55/2.02    spl6_78 | ~spl6_38 | ~spl6_47),
% 12.55/2.02    inference(avatar_split_clause,[],[f863,f557,f474,f907])).
% 12.55/2.02  fof(f863,plain,(
% 12.55/2.02    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_38 | ~spl6_47)),
% 12.55/2.02    inference(backward_demodulation,[],[f558,f476])).
% 12.55/2.02  fof(f558,plain,(
% 12.55/2.02    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_47),
% 12.55/2.02    inference(avatar_component_clause,[],[f557])).
% 12.55/2.02  fof(f900,plain,(
% 12.55/2.02    spl6_76 | ~spl6_16 | ~spl6_38),
% 12.55/2.02    inference(avatar_split_clause,[],[f861,f474,f228,f897])).
% 12.55/2.02  fof(f861,plain,(
% 12.55/2.02    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_16 | ~spl6_38)),
% 12.55/2.02    inference(backward_demodulation,[],[f230,f476])).
% 12.55/2.02  fof(f890,plain,(
% 12.55/2.02    spl6_74 | ~spl6_8 | ~spl6_38),
% 12.55/2.02    inference(avatar_split_clause,[],[f859,f474,f185,f887])).
% 12.55/2.02  fof(f859,plain,(
% 12.55/2.02    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl6_8 | ~spl6_38)),
% 12.55/2.02    inference(backward_demodulation,[],[f187,f476])).
% 12.55/2.02  fof(f835,plain,(
% 12.55/2.02    ~spl6_42 | ~spl6_43 | ~spl6_44 | ~spl6_45 | ~spl6_16 | spl6_46 | ~spl6_15 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_17),
% 12.55/2.02    inference(avatar_split_clause,[],[f730,f234,f200,f195,f190,f222,f529,f228,f525,f521,f517,f513])).
% 12.55/2.02  fof(f730,plain,(
% 12.55/2.02    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_17)),
% 12.55/2.02    inference(subsumption_resolution,[],[f729,f202])).
% 12.55/2.02  fof(f729,plain,(
% 12.55/2.02    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_17)),
% 12.55/2.02    inference(subsumption_resolution,[],[f728,f197])).
% 12.55/2.02  fof(f728,plain,(
% 12.55/2.02    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_17)),
% 12.55/2.02    inference(subsumption_resolution,[],[f502,f192])).
% 12.55/2.02  fof(f502,plain,(
% 12.55/2.02    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_17),
% 12.55/2.02    inference(resolution,[],[f146,f236])).
% 12.55/2.02  fof(f834,plain,(
% 12.55/2.02    ~spl6_42 | ~spl6_43 | ~spl6_44 | ~spl6_45 | ~spl6_16 | spl6_15 | ~spl6_46 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_17),
% 12.55/2.02    inference(avatar_split_clause,[],[f753,f234,f200,f195,f190,f529,f222,f228,f525,f521,f517,f513])).
% 12.55/2.02  fof(f753,plain,(
% 12.55/2.02    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_17)),
% 12.55/2.02    inference(subsumption_resolution,[],[f752,f202])).
% 12.55/2.02  fof(f752,plain,(
% 12.55/2.02    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_10 | ~spl6_17)),
% 12.55/2.02    inference(subsumption_resolution,[],[f751,f197])).
% 12.55/2.02  fof(f751,plain,(
% 12.55/2.02    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_9 | ~spl6_17)),
% 12.55/2.02    inference(subsumption_resolution,[],[f491,f192])).
% 12.55/2.02  fof(f491,plain,(
% 12.55/2.02    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_17),
% 12.55/2.02    inference(resolution,[],[f145,f236])).
% 12.55/2.02  fof(f672,plain,(
% 12.55/2.02    spl6_61 | ~spl6_26 | ~spl6_52),
% 12.55/2.02    inference(avatar_split_clause,[],[f614,f590,f320,f669])).
% 12.55/2.02  fof(f614,plain,(
% 12.55/2.02    v4_relat_1(sK2,k1_relat_1(sK2)) | (~spl6_26 | ~spl6_52)),
% 12.55/2.02    inference(backward_demodulation,[],[f322,f592])).
% 12.55/2.02  fof(f322,plain,(
% 12.55/2.02    v4_relat_1(sK2,u1_struct_0(sK0)) | ~spl6_26),
% 12.55/2.02    inference(avatar_component_clause,[],[f320])).
% 12.55/2.02  fof(f642,plain,(
% 12.55/2.02    spl6_55 | ~spl6_8 | ~spl6_52),
% 12.55/2.02    inference(avatar_split_clause,[],[f608,f590,f185,f639])).
% 12.55/2.02  fof(f608,plain,(
% 12.55/2.02    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl6_8 | ~spl6_52)),
% 12.55/2.02    inference(backward_demodulation,[],[f187,f592])).
% 12.55/2.02  fof(f637,plain,(
% 12.55/2.02    spl6_54 | ~spl6_7 | ~spl6_52),
% 12.55/2.02    inference(avatar_split_clause,[],[f607,f590,f180,f634])).
% 12.55/2.02  fof(f607,plain,(
% 12.55/2.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl6_7 | ~spl6_52)),
% 12.55/2.02    inference(backward_demodulation,[],[f182,f592])).
% 12.55/2.02  fof(f595,plain,(
% 12.55/2.02    spl6_52 | ~spl6_7 | ~spl6_37),
% 12.55/2.02    inference(avatar_split_clause,[],[f594,f470,f180,f590])).
% 12.55/2.02  fof(f594,plain,(
% 12.55/2.02    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl6_7 | ~spl6_37)),
% 12.55/2.02    inference(subsumption_resolution,[],[f586,f182])).
% 12.55/2.02  fof(f586,plain,(
% 12.55/2.02    u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_37),
% 12.55/2.02    inference(superposition,[],[f100,f472])).
% 12.55/2.02  fof(f472,plain,(
% 12.55/2.02    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl6_37),
% 12.55/2.02    inference(avatar_component_clause,[],[f470])).
% 12.55/2.02  fof(f583,plain,(
% 12.55/2.02    ~spl6_10 | ~spl6_11 | spl6_47),
% 12.55/2.02    inference(avatar_contradiction_clause,[],[f582])).
% 12.55/2.02  fof(f582,plain,(
% 12.55/2.02    $false | (~spl6_10 | ~spl6_11 | spl6_47)),
% 12.55/2.02    inference(subsumption_resolution,[],[f581,f202])).
% 12.55/2.02  fof(f581,plain,(
% 12.55/2.02    ~v2_pre_topc(sK1) | (~spl6_10 | spl6_47)),
% 12.55/2.02    inference(subsumption_resolution,[],[f579,f197])).
% 12.55/2.02  fof(f579,plain,(
% 12.55/2.02    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl6_47),
% 12.55/2.02    inference(resolution,[],[f559,f110])).
% 12.55/2.02  fof(f559,plain,(
% 12.55/2.02    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_47),
% 12.55/2.02    inference(avatar_component_clause,[],[f557])).
% 12.55/2.02  fof(f545,plain,(
% 12.55/2.02    ~spl6_12 | ~spl6_13 | spl6_42),
% 12.55/2.02    inference(avatar_contradiction_clause,[],[f544])).
% 12.55/2.02  fof(f544,plain,(
% 12.55/2.02    $false | (~spl6_12 | ~spl6_13 | spl6_42)),
% 12.55/2.02    inference(subsumption_resolution,[],[f543,f212])).
% 12.55/2.02  fof(f543,plain,(
% 12.55/2.02    ~v2_pre_topc(sK0) | (~spl6_12 | spl6_42)),
% 12.55/2.02    inference(subsumption_resolution,[],[f541,f207])).
% 12.55/2.02  fof(f541,plain,(
% 12.55/2.02    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl6_42),
% 12.55/2.02    inference(resolution,[],[f515,f110])).
% 12.55/2.02  fof(f515,plain,(
% 12.55/2.02    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl6_42),
% 12.55/2.02    inference(avatar_component_clause,[],[f513])).
% 12.55/2.02  fof(f501,plain,(
% 12.55/2.02    ~spl6_35 | spl6_41),
% 12.55/2.02    inference(avatar_split_clause,[],[f497,f499,f453])).
% 12.55/2.02  fof(f497,plain,(
% 12.55/2.02    ( ! [X2,X1] : (~v5_pre_topc(k1_xboole_0,X1,X2) | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 12.55/2.02    inference(subsumption_resolution,[],[f493,f118])).
% 12.55/2.02  fof(f493,plain,(
% 12.55/2.02    ( ! [X2,X1] : (~v5_pre_topc(k1_xboole_0,X1,X2) | v5_pre_topc(k1_xboole_0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 12.55/2.02    inference(resolution,[],[f145,f118])).
% 12.55/2.02  fof(f487,plain,(
% 12.55/2.02    spl6_39 | spl6_40 | ~spl6_16 | ~spl6_17),
% 12.55/2.02    inference(avatar_split_clause,[],[f478,f234,f228,f484,f480])).
% 12.55/2.02  fof(f478,plain,(
% 12.55/2.02    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl6_16 | ~spl6_17)),
% 12.55/2.02    inference(subsumption_resolution,[],[f461,f230])).
% 12.55/2.02  fof(f461,plain,(
% 12.55/2.02    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl6_17),
% 12.55/2.02    inference(resolution,[],[f94,f236])).
% 12.55/2.02  fof(f459,plain,(
% 12.55/2.02    ~spl6_35 | spl6_36),
% 12.55/2.02    inference(avatar_split_clause,[],[f431,f457,f453])).
% 12.55/2.02  fof(f431,plain,(
% 12.55/2.02    ( ! [X2,X1] : (~v1_funct_2(k1_xboole_0,X1,X2) | ~v1_funct_1(k1_xboole_0) | v1_partfun1(k1_xboole_0,X1) | v1_xboole_0(X2)) )),
% 12.55/2.02    inference(resolution,[],[f120,f118])).
% 12.55/2.02  fof(f120,plain,(
% 12.55/2.02    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 12.55/2.02    inference(cnf_transformation,[],[f51])).
% 12.55/2.02  fof(f51,plain,(
% 12.55/2.02    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 12.55/2.02    inference(flattening,[],[f50])).
% 12.55/2.02  fof(f50,plain,(
% 12.55/2.02    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 12.55/2.02    inference(ennf_transformation,[],[f16])).
% 12.55/2.02  fof(f16,axiom,(
% 12.55/2.02    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 12.55/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 12.55/2.02  fof(f368,plain,(
% 12.55/2.02    ~spl6_25),
% 12.55/2.02    inference(avatar_contradiction_clause,[],[f367])).
% 12.55/2.02  fof(f367,plain,(
% 12.55/2.02    $false | ~spl6_25),
% 12.55/2.02    inference(resolution,[],[f306,f116])).
% 12.55/2.02  fof(f116,plain,(
% 12.55/2.02    ( ! [X0] : (v1_xboole_0(sK4(X0))) )),
% 12.55/2.02    inference(cnf_transformation,[],[f72])).
% 12.55/2.02  fof(f72,plain,(
% 12.55/2.02    ! [X0] : (v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)))),
% 12.55/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f6,f71])).
% 12.55/2.02  fof(f71,plain,(
% 12.55/2.02    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))))),
% 12.55/2.02    introduced(choice_axiom,[])).
% 12.55/2.02  fof(f6,axiom,(
% 12.55/2.02    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.55/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 12.55/2.02  fof(f306,plain,(
% 12.55/2.02    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl6_25),
% 12.55/2.02    inference(avatar_component_clause,[],[f305])).
% 12.55/2.02  fof(f305,plain,(
% 12.55/2.02    spl6_25 <=> ! [X0] : ~v1_xboole_0(X0)),
% 12.55/2.02    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 12.55/2.02  fof(f328,plain,(
% 12.55/2.02    spl6_27 | ~spl6_17),
% 12.55/2.02    inference(avatar_split_clause,[],[f312,f234,f325])).
% 12.55/2.02  fof(f312,plain,(
% 12.55/2.02    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | ~spl6_17),
% 12.55/2.02    inference(resolution,[],[f127,f236])).
% 12.55/2.02  fof(f307,plain,(
% 12.55/2.02    spl6_24 | spl6_25),
% 12.55/2.02    inference(avatar_split_clause,[],[f294,f305,f302])).
% 12.55/2.02  fof(f294,plain,(
% 12.55/2.02    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 12.55/2.02    inference(resolution,[],[f112,f118])).
% 12.55/2.02  fof(f284,plain,(
% 12.55/2.02    spl6_23),
% 12.55/2.02    inference(avatar_split_clause,[],[f270,f281])).
% 12.55/2.02  fof(f270,plain,(
% 12.55/2.02    v1_relat_1(k1_xboole_0)),
% 12.55/2.02    inference(resolution,[],[f128,f118])).
% 12.55/2.02  fof(f278,plain,(
% 12.55/2.02    spl6_22 | ~spl6_7),
% 12.55/2.02    inference(avatar_split_clause,[],[f267,f180,f275])).
% 12.55/2.02  fof(f267,plain,(
% 12.55/2.02    v1_relat_1(sK2) | ~spl6_7),
% 12.55/2.02    inference(resolution,[],[f128,f182])).
% 12.55/2.02  fof(f245,plain,(
% 12.55/2.02    spl6_18),
% 12.55/2.02    inference(avatar_split_clause,[],[f239,f241])).
% 12.55/2.02  fof(f239,plain,(
% 12.55/2.02    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 12.55/2.02    inference(superposition,[],[f126,f141])).
% 12.55/2.02  fof(f237,plain,(
% 12.55/2.02    spl6_17 | ~spl6_3 | ~spl6_4),
% 12.55/2.02    inference(avatar_split_clause,[],[f232,f165,f160,f234])).
% 12.55/2.02  fof(f165,plain,(
% 12.55/2.02    spl6_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 12.55/2.02    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 12.55/2.02  fof(f232,plain,(
% 12.55/2.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_3 | ~spl6_4)),
% 12.55/2.02    inference(forward_demodulation,[],[f167,f162])).
% 12.55/2.02  fof(f167,plain,(
% 12.55/2.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_4),
% 12.55/2.02    inference(avatar_component_clause,[],[f165])).
% 12.55/2.02  fof(f231,plain,(
% 12.55/2.02    spl6_16 | ~spl6_3 | ~spl6_5),
% 12.55/2.02    inference(avatar_split_clause,[],[f226,f170,f160,f228])).
% 12.55/2.02  fof(f170,plain,(
% 12.55/2.02    spl6_5 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.02    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 12.55/2.02  fof(f226,plain,(
% 12.55/2.02    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_3 | ~spl6_5)),
% 12.55/2.02    inference(forward_demodulation,[],[f172,f162])).
% 12.55/2.02  fof(f172,plain,(
% 12.55/2.02    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_5),
% 12.55/2.02    inference(avatar_component_clause,[],[f170])).
% 12.55/2.02  fof(f225,plain,(
% 12.55/2.02    spl6_15 | ~spl6_2 | ~spl6_3),
% 12.55/2.02    inference(avatar_split_clause,[],[f220,f160,f154,f222])).
% 12.55/2.02  fof(f220,plain,(
% 12.55/2.02    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3)),
% 12.55/2.02    inference(forward_demodulation,[],[f155,f162])).
% 12.55/2.02  fof(f218,plain,(
% 12.55/2.02    spl6_14),
% 12.55/2.02    inference(avatar_split_clause,[],[f121,f215])).
% 12.55/2.02  fof(f121,plain,(
% 12.55/2.02    v1_xboole_0(k1_xboole_0)),
% 12.55/2.02    inference(cnf_transformation,[],[f2])).
% 12.55/2.02  fof(f2,axiom,(
% 12.55/2.02    v1_xboole_0(k1_xboole_0)),
% 12.55/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 12.55/2.02  fof(f213,plain,(
% 12.55/2.02    spl6_13),
% 12.55/2.02    inference(avatar_split_clause,[],[f77,f210])).
% 12.55/2.02  fof(f77,plain,(
% 12.55/2.02    v2_pre_topc(sK0)),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f62,plain,(
% 12.55/2.02    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 12.55/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f61,f60,f59,f58])).
% 12.55/2.02  fof(f58,plain,(
% 12.55/2.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 12.55/2.02    introduced(choice_axiom,[])).
% 12.55/2.02  fof(f59,plain,(
% 12.55/2.02    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 12.55/2.02    introduced(choice_axiom,[])).
% 12.55/2.02  fof(f60,plain,(
% 12.55/2.02    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 12.55/2.02    introduced(choice_axiom,[])).
% 12.55/2.02  fof(f61,plain,(
% 12.55/2.02    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 12.55/2.02    introduced(choice_axiom,[])).
% 12.55/2.02  fof(f57,plain,(
% 12.55/2.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.55/2.02    inference(flattening,[],[f56])).
% 12.55/2.02  fof(f56,plain,(
% 12.55/2.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.55/2.02    inference(nnf_transformation,[],[f31])).
% 12.55/2.02  fof(f31,plain,(
% 12.55/2.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.55/2.02    inference(flattening,[],[f30])).
% 12.55/2.02  fof(f30,plain,(
% 12.55/2.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 12.55/2.02    inference(ennf_transformation,[],[f26])).
% 12.55/2.02  fof(f26,negated_conjecture,(
% 12.55/2.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 12.55/2.02    inference(negated_conjecture,[],[f25])).
% 12.55/2.02  fof(f25,conjecture,(
% 12.55/2.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 12.55/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 12.55/2.02  fof(f208,plain,(
% 12.55/2.02    spl6_12),
% 12.55/2.02    inference(avatar_split_clause,[],[f78,f205])).
% 12.55/2.02  fof(f78,plain,(
% 12.55/2.02    l1_pre_topc(sK0)),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f203,plain,(
% 12.55/2.02    spl6_11),
% 12.55/2.02    inference(avatar_split_clause,[],[f79,f200])).
% 12.55/2.02  fof(f79,plain,(
% 12.55/2.02    v2_pre_topc(sK1)),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f198,plain,(
% 12.55/2.02    spl6_10),
% 12.55/2.02    inference(avatar_split_clause,[],[f80,f195])).
% 12.55/2.02  fof(f80,plain,(
% 12.55/2.02    l1_pre_topc(sK1)),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f193,plain,(
% 12.55/2.02    spl6_9),
% 12.55/2.02    inference(avatar_split_clause,[],[f81,f190])).
% 12.55/2.02  fof(f81,plain,(
% 12.55/2.02    v1_funct_1(sK2)),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f188,plain,(
% 12.55/2.02    spl6_8),
% 12.55/2.02    inference(avatar_split_clause,[],[f82,f185])).
% 12.55/2.02  fof(f82,plain,(
% 12.55/2.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f183,plain,(
% 12.55/2.02    spl6_7),
% 12.55/2.02    inference(avatar_split_clause,[],[f83,f180])).
% 12.55/2.02  fof(f83,plain,(
% 12.55/2.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f173,plain,(
% 12.55/2.02    spl6_5),
% 12.55/2.02    inference(avatar_split_clause,[],[f85,f170])).
% 12.55/2.02  fof(f85,plain,(
% 12.55/2.02    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f168,plain,(
% 12.55/2.02    spl6_4),
% 12.55/2.02    inference(avatar_split_clause,[],[f86,f165])).
% 12.55/2.02  fof(f86,plain,(
% 12.55/2.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f163,plain,(
% 12.55/2.02    spl6_3),
% 12.55/2.02    inference(avatar_split_clause,[],[f87,f160])).
% 12.55/2.02  fof(f87,plain,(
% 12.55/2.02    sK2 = sK3),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f158,plain,(
% 12.55/2.02    spl6_1 | spl6_2),
% 12.55/2.02    inference(avatar_split_clause,[],[f88,f154,f150])).
% 12.55/2.02  fof(f88,plain,(
% 12.55/2.02    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  fof(f157,plain,(
% 12.55/2.02    ~spl6_1 | ~spl6_2),
% 12.55/2.02    inference(avatar_split_clause,[],[f89,f154,f150])).
% 12.55/2.02  fof(f89,plain,(
% 12.55/2.02    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 12.55/2.02    inference(cnf_transformation,[],[f62])).
% 12.55/2.02  % SZS output end Proof for theBenchmark
% 12.55/2.02  % (24689)------------------------------
% 12.55/2.02  % (24689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.55/2.02  % (24689)Termination reason: Refutation
% 12.55/2.02  
% 12.55/2.02  % (24689)Memory used [KB]: 14583
% 12.55/2.02  % (24689)Time elapsed: 1.381 s
% 12.55/2.02  % (24689)------------------------------
% 12.55/2.02  % (24689)------------------------------
% 12.55/2.02  % (24629)Success in time 1.653 s
%------------------------------------------------------------------------------
