%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:35 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  275 ( 606 expanded)
%              Number of leaves         :   63 ( 297 expanded)
%              Depth                    :   15
%              Number of atoms          : 1285 (2819 expanded)
%              Number of equality atoms :  125 ( 218 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f124,f128,f132,f136,f140,f148,f152,f156,f174,f187,f191,f245,f277,f279,f325,f330,f348,f353,f442,f454,f594,f607,f614,f647,f1272,f1353,f1365,f1405,f1416,f1421,f1427,f1477,f1481,f1870,f2463,f2640,f2645,f2647,f2679,f2721,f3209])).

fof(f3209,plain,
    ( ~ spl6_6
    | spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | spl6_306
    | ~ spl6_303 ),
    inference(avatar_split_clause,[],[f3207,f2677,f2719,f146,f150,f154,f138])).

fof(f138,plain,
    ( spl6_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f154,plain,
    ( spl6_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f150,plain,
    ( spl6_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f146,plain,
    ( spl6_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f2719,plain,
    ( spl6_306
  <=> r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_306])])).

fof(f2677,plain,
    ( spl6_303
  <=> r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_303])])).

fof(f3207,plain,
    ( r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl6_303 ),
    inference(superposition,[],[f2678,f242])).

fof(f242,plain,(
    ! [X0,X1] :
      ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
    ! [X0,X1] :
      ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f92,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f2678,plain,
    ( r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),sK3)
    | ~ spl6_303 ),
    inference(avatar_component_clause,[],[f2677])).

fof(f2721,plain,
    ( ~ spl6_306
    | spl6_1
    | ~ spl6_154 ),
    inference(avatar_split_clause,[],[f1366,f1363,f118,f2719])).

fof(f118,plain,
    ( spl6_1
  <=> r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1363,plain,
    ( spl6_154
  <=> k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_154])])).

fof(f1366,plain,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK3)
    | spl6_1
    | ~ spl6_154 ),
    inference(superposition,[],[f119,f1364])).

fof(f1364,plain,
    ( k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ spl6_154 ),
    inference(avatar_component_clause,[],[f1363])).

fof(f119,plain,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f2679,plain,
    ( ~ spl6_40
    | ~ spl6_21
    | spl6_303
    | ~ spl6_3
    | ~ spl6_13
    | ~ spl6_161 ),
    inference(avatar_split_clause,[],[f1433,f1425,f185,f126,f2677,f227,f319])).

fof(f319,plain,
    ( spl6_40
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f227,plain,
    ( spl6_21
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f126,plain,
    ( spl6_3
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f185,plain,
    ( spl6_13
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f1425,plain,
    ( spl6_161
  <=> ! [X1] :
        ( r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X1)),k7_tmap_1(sK0,u1_struct_0(X1)),sK2),sK3)
        | ~ l1_struct_0(X1)
        | ~ r1_tsep_1(X1,sK2)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).

fof(f1433,plain,
    ( r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl6_3
    | ~ spl6_13
    | ~ spl6_161 ),
    inference(forward_demodulation,[],[f1431,f186])).

fof(f186,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f1431,plain,
    ( r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl6_3
    | ~ spl6_161 ),
    inference(resolution,[],[f1430,f127])).

fof(f127,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f1430,plain,
    ( ! [X0] :
        ( ~ r1_tsep_1(X0,sK2)
        | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X0)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X0)),k7_tmap_1(sK0,u1_struct_0(X0)),sK2),sK3)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_161 ),
    inference(resolution,[],[f1426,f79])).

fof(f79,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f1426,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X1)),k7_tmap_1(sK0,u1_struct_0(X1)),sK2),sK3)
        | ~ r1_tsep_1(X1,sK2)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_161 ),
    inference(avatar_component_clause,[],[f1425])).

fof(f2647,plain,
    ( ~ spl6_8
    | spl6_300 ),
    inference(avatar_split_clause,[],[f2646,f2643,f146])).

fof(f2643,plain,
    ( spl6_300
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_300])])).

fof(f2646,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_300 ),
    inference(resolution,[],[f2644,f79])).

fof(f2644,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_300 ),
    inference(avatar_component_clause,[],[f2643])).

fof(f2645,plain,
    ( spl6_10
    | ~ spl6_300
    | ~ spl6_130 ),
    inference(avatar_split_clause,[],[f2641,f1079,f2643,f154])).

fof(f1079,plain,
    ( spl6_130
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).

fof(f2641,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_130 ),
    inference(resolution,[],[f2459,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f2459,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_130 ),
    inference(avatar_component_clause,[],[f1079])).

fof(f2640,plain,
    ( ~ spl6_74
    | ~ spl6_79
    | ~ spl6_59
    | ~ spl6_275 ),
    inference(avatar_split_clause,[],[f2639,f2461,f452,f645,f605])).

fof(f605,plain,
    ( spl6_74
  <=> v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f645,plain,
    ( spl6_79
  <=> m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f452,plain,
    ( spl6_59
  <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f2461,plain,
    ( spl6_275
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_275])])).

fof(f2639,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_59
    | ~ spl6_275 ),
    inference(resolution,[],[f2462,f453])).

fof(f453,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f452])).

fof(f2462,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) )
    | ~ spl6_275 ),
    inference(avatar_component_clause,[],[f2461])).

fof(f2463,plain,
    ( spl6_130
    | ~ spl6_59
    | ~ spl6_74
    | ~ spl6_79
    | spl6_275
    | spl6_148 ),
    inference(avatar_split_clause,[],[f2458,f1318,f2461,f645,f605,f452,f1079])).

fof(f1318,plain,
    ( spl6_148
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).

fof(f2458,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl6_148 ),
    inference(duplicate_literal_removal,[],[f2457])).

fof(f2457,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | spl6_148 ),
    inference(resolution,[],[f1855,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

fof(f1855,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | spl6_148 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f1870,plain,
    ( ~ spl6_59
    | spl6_154
    | ~ spl6_79
    | ~ spl6_74
    | ~ spl6_148
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_152
    | ~ spl6_170
    | ~ spl6_171 ),
    inference(avatar_split_clause,[],[f1869,f1479,f1475,f1351,f346,f138,f1318,f605,f645,f1363,f452])).

fof(f346,plain,
    ( spl6_43
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f1351,plain,
    ( spl6_152
  <=> ! [X5,X4] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X4,X5))),X5,k7_tmap_1(sK0,sK5(sK0,X4,X5)))
        | k9_tmap_1(sK0,X4) = X5
        | ~ m1_pre_topc(X4,sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_152])])).

fof(f1475,plain,
    ( spl6_170
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_170])])).

fof(f1479,plain,
    ( spl6_171
  <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_171])])).

fof(f1869,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_152
    | ~ spl6_170
    | ~ spl6_171 ),
    inference(forward_demodulation,[],[f1851,f1476])).

fof(f1476,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))))
    | ~ spl6_170 ),
    inference(avatar_component_clause,[],[f1475])).

fof(f1851,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_152
    | ~ spl6_171 ),
    inference(superposition,[],[f1650,f1480])).

fof(f1480,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))
    | ~ spl6_171 ),
    inference(avatar_component_clause,[],[f1479])).

fof(f1650,plain,
    ( ! [X1] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,X1))),X1,k7_tmap_1(sK0,sK5(sK0,sK1,X1)))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | k9_tmap_1(sK0,sK1) = X1
        | ~ v1_funct_1(X1) )
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_152 ),
    inference(forward_demodulation,[],[f1649,f347])).

fof(f347,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f346])).

fof(f1649,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,X1))),X1,k7_tmap_1(sK0,sK5(sK0,sK1,X1)))
        | k9_tmap_1(sK0,sK1) = X1
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) )
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_152 ),
    inference(forward_demodulation,[],[f1648,f347])).

fof(f1648,plain,
    ( ! [X1] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,X1))),X1,k7_tmap_1(sK0,sK5(sK0,sK1,X1)))
        | k9_tmap_1(sK0,sK1) = X1
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) )
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_152 ),
    inference(forward_demodulation,[],[f1642,f347])).

fof(f1642,plain,
    ( ! [X1] :
        ( k9_tmap_1(sK0,sK1) = X1
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,X1))),X1,k7_tmap_1(sK0,sK5(sK0,sK1,X1)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) )
    | ~ spl6_6
    | ~ spl6_152 ),
    inference(resolution,[],[f1352,f139])).

fof(f139,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1352,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(X4,sK0)
        | k9_tmap_1(sK0,X4) = X5
        | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X4,X5))),X5,k7_tmap_1(sK0,sK5(sK0,X4,X5)))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))))) )
    | ~ spl6_152 ),
    inference(avatar_component_clause,[],[f1351])).

fof(f1481,plain,
    ( spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | spl6_171
    | ~ spl6_153 ),
    inference(avatar_split_clause,[],[f1447,f1360,f1479,f146,f150,f154])).

fof(f1360,plain,
    ( spl6_153
  <=> m1_subset_1(sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_153])])).

fof(f1447,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_153 ),
    inference(resolution,[],[f1361,f92])).

fof(f1361,plain,
    ( m1_subset_1(sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_153 ),
    inference(avatar_component_clause,[],[f1360])).

fof(f1477,plain,
    ( spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | spl6_170
    | ~ spl6_153 ),
    inference(avatar_split_clause,[],[f1446,f1360,f1475,f146,f150,f154])).

fof(f1446,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_153 ),
    inference(resolution,[],[f1361,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f1427,plain,
    ( ~ spl6_159
    | spl6_161
    | ~ spl6_158 ),
    inference(avatar_split_clause,[],[f1423,f1403,f1425,f1409])).

fof(f1409,plain,
    ( spl6_159
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_159])])).

fof(f1403,plain,
    ( spl6_158
  <=> ! [X0] :
        ( ~ r1_xboole_0(u1_struct_0(sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_158])])).

fof(f1423,plain,
    ( ! [X1] :
        ( r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X1)),k7_tmap_1(sK0,u1_struct_0(X1)),sK2),sK3)
        | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tsep_1(X1,sK2)
        | ~ l1_struct_0(sK2)
        | ~ l1_struct_0(X1) )
    | ~ spl6_158 ),
    inference(resolution,[],[f1407,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f1407,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,u1_struct_0(sK2))
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_158 ),
    inference(resolution,[],[f1404,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1404,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(u1_struct_0(sK2),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK3) )
    | ~ spl6_158 ),
    inference(avatar_component_clause,[],[f1403])).

fof(f1421,plain,
    ( ~ spl6_8
    | ~ spl6_4
    | spl6_37 ),
    inference(avatar_split_clause,[],[f1418,f309,f130,f146])).

fof(f130,plain,
    ( spl6_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f309,plain,
    ( spl6_37
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f1418,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_4
    | spl6_37 ),
    inference(resolution,[],[f1417,f131])).

fof(f131,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1417,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl6_37 ),
    inference(resolution,[],[f310,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f310,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_37 ),
    inference(avatar_component_clause,[],[f309])).

fof(f1416,plain,
    ( ~ spl6_37
    | spl6_159 ),
    inference(avatar_split_clause,[],[f1415,f1409,f309])).

fof(f1415,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_159 ),
    inference(resolution,[],[f1410,f79])).

fof(f1410,plain,
    ( ~ l1_struct_0(sK2)
    | spl6_159 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f1405,plain,
    ( spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | spl6_158
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f1399,f134,f130,f122,f1403,f146,f150,f154])).

fof(f122,plain,
    ( spl6_2
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f134,plain,
    ( spl6_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1399,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(u1_struct_0(sK2),X0)
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5 ),
    inference(resolution,[],[f1398,f131])).

fof(f1398,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK2,X1)
        | ~ r1_xboole_0(u1_struct_0(sK2),X0)
        | r1_tmap_1(sK2,k6_tmap_1(X1,X0),k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK2),sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_2
    | spl6_5 ),
    inference(resolution,[],[f1038,f123])).

fof(f123,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1038,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_xboole_0(u1_struct_0(sK2),X1)
        | ~ m1_pre_topc(sK2,X2)
        | r1_tmap_1(sK2,k6_tmap_1(X2,X1),k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),sK2),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | spl6_5 ),
    inference(resolution,[],[f95,f135])).

fof(f135,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X2)) )
              | ~ r1_xboole_0(u1_struct_0(X2),X1)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f1365,plain,
    ( ~ spl6_79
    | spl6_153
    | spl6_154
    | ~ spl6_74
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_59
    | ~ spl6_144 ),
    inference(avatar_split_clause,[],[f1358,f1270,f452,f346,f138,f605,f1363,f1360,f645])).

fof(f1270,plain,
    ( spl6_144
  <=> ! [X5,X4] :
        ( m1_subset_1(sK5(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_tmap_1(sK0,X4) = X5
        | ~ m1_pre_topc(X4,sK0)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).

fof(f1358,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | m1_subset_1(sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_59
    | ~ spl6_144 ),
    inference(resolution,[],[f1291,f453])).

fof(f1291,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | k9_tmap_1(sK0,sK1) = X1
        | m1_subset_1(sK5(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_144 ),
    inference(forward_demodulation,[],[f1290,f347])).

fof(f1290,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0))
        | k9_tmap_1(sK0,sK1) = X1
        | m1_subset_1(sK5(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) )
    | ~ spl6_6
    | ~ spl6_43
    | ~ spl6_144 ),
    inference(forward_demodulation,[],[f1286,f347])).

fof(f1286,plain,
    ( ! [X1] :
        ( k9_tmap_1(sK0,sK1) = X1
        | m1_subset_1(sK5(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) )
    | ~ spl6_6
    | ~ spl6_144 ),
    inference(resolution,[],[f1271,f139])).

fof(f1271,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(X4,sK0)
        | k9_tmap_1(sK0,X4) = X5
        | m1_subset_1(sK5(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))))) )
    | ~ spl6_144 ),
    inference(avatar_component_clause,[],[f1270])).

fof(f1353,plain,
    ( ~ spl6_9
    | ~ spl6_8
    | spl6_152
    | spl6_10 ),
    inference(avatar_split_clause,[],[f1349,f154,f1351,f146,f150])).

fof(f1349,plain,
    ( ! [X4,X5] :
        ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X4,X5))),X5,k7_tmap_1(sK0,sK5(sK0,X4,X5)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))))
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(X4,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k9_tmap_1(sK0,X4) = X5 )
    | spl6_10 ),
    inference(resolution,[],[f91,f155])).

fof(f155,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
                    & u1_struct_0(X1) = sK5(X0,X1,X2)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f64,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
        & u1_struct_0(X1) = sK5(X0,X1,X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f1272,plain,
    ( ~ spl6_9
    | ~ spl6_8
    | spl6_144
    | spl6_10 ),
    inference(avatar_split_clause,[],[f1268,f154,f1270,f146,f150])).

fof(f1268,plain,
    ( ! [X4,X5] :
        ( m1_subset_1(sK5(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))))
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))
        | ~ v1_funct_1(X5)
        | ~ m1_pre_topc(X4,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | k9_tmap_1(sK0,X4) = X5 )
    | spl6_10 ),
    inference(resolution,[],[f89,f155])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k9_tmap_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f647,plain,
    ( spl6_79
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_44
    | ~ spl6_57
    | ~ spl6_75 ),
    inference(avatar_split_clause,[],[f643,f612,f440,f351,f259,f189,f645])).

fof(f189,plain,
    ( spl6_14
  <=> k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f259,plain,
    ( spl6_27
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f351,plain,
    ( spl6_44
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f440,plain,
    ( spl6_57
  <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f612,plain,
    ( spl6_75
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f643,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_44
    | ~ spl6_57
    | ~ spl6_75 ),
    inference(forward_demodulation,[],[f642,f441])).

fof(f441,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f440])).

fof(f642,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_44
    | ~ spl6_75 ),
    inference(forward_demodulation,[],[f641,f352])).

fof(f352,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f351])).

fof(f641,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))))
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_75 ),
    inference(forward_demodulation,[],[f636,f190])).

fof(f190,plain,
    ( k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f636,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))))))
    | ~ spl6_27
    | ~ spl6_75 ),
    inference(resolution,[],[f613,f434])).

fof(f434,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f259])).

fof(f613,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k7_tmap_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2))))) )
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f612])).

fof(f614,plain,
    ( ~ spl6_9
    | ~ spl6_8
    | spl6_75
    | spl6_10 ),
    inference(avatar_split_clause,[],[f610,f154,f612,f146,f150])).

fof(f610,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_subset_1(k7_tmap_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2))))) )
    | spl6_10 ),
    inference(resolution,[],[f110,f155])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f607,plain,
    ( spl6_74
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_44
    | ~ spl6_57
    | ~ spl6_72 ),
    inference(avatar_split_clause,[],[f603,f592,f440,f351,f259,f189,f605])).

fof(f592,plain,
    ( spl6_72
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_funct_2(k7_tmap_1(sK0,X2),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f603,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_44
    | ~ spl6_57
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f602,f441])).

fof(f602,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_44
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f601,f352])).

fof(f601,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0)))
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f596,f190])).

fof(f596,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))))
    | ~ spl6_27
    | ~ spl6_72 ),
    inference(resolution,[],[f593,f434])).

fof(f593,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_funct_2(k7_tmap_1(sK0,X2),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2))) )
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f592])).

fof(f594,plain,
    ( ~ spl6_9
    | ~ spl6_8
    | spl6_72
    | spl6_10 ),
    inference(avatar_split_clause,[],[f590,f154,f592,f146,f150])).

fof(f590,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v1_funct_2(k7_tmap_1(sK0,X2),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2))) )
    | spl6_10 ),
    inference(resolution,[],[f109,f155])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f454,plain,
    ( spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_27
    | spl6_59
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f450,f440,f452,f259,f146,f150,f154])).

fof(f450,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_57 ),
    inference(superposition,[],[f108,f441])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f442,plain,
    ( spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | spl6_57
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f437,f259,f440,f146,f150,f154])).

fof(f437,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_27 ),
    inference(resolution,[],[f434,f92])).

fof(f353,plain,
    ( ~ spl6_8
    | spl6_44
    | ~ spl6_14
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f349,f323,f189,f351,f146])).

fof(f323,plain,
    ( spl6_41
  <=> ! [X2] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X2)))
        | ~ m1_pre_topc(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f349,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_14
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f338,f190])).

fof(f338,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_41 ),
    inference(resolution,[],[f324,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f324,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X2))) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f323])).

fof(f348,plain,
    ( spl6_43
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f344,f323,f185,f138,f346])).

fof(f344,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f337,f186])).

fof(f337,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_6
    | ~ spl6_41 ),
    inference(resolution,[],[f324,f139])).

fof(f330,plain,
    ( ~ spl6_8
    | ~ spl6_6
    | spl6_40 ),
    inference(avatar_split_clause,[],[f327,f319,f138,f146])).

fof(f327,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_6
    | spl6_40 ),
    inference(resolution,[],[f326,f139])).

fof(f326,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl6_40 ),
    inference(resolution,[],[f320,f81])).

fof(f320,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f319])).

fof(f325,plain,
    ( spl6_41
    | ~ spl6_9
    | ~ spl6_8
    | spl6_10 ),
    inference(avatar_split_clause,[],[f301,f154,f146,f150,f323])).

fof(f301,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X2)))
        | ~ m1_pre_topc(X2,sK0) )
    | spl6_10 ),
    inference(resolution,[],[f290,f155])).

fof(f290,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f93,f82])).

fof(f279,plain,
    ( ~ spl6_8
    | spl6_31 ),
    inference(avatar_split_clause,[],[f278,f275,f146])).

fof(f275,plain,
    ( spl6_31
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f278,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_31 ),
    inference(resolution,[],[f276,f80])).

fof(f276,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f275])).

fof(f277,plain,
    ( ~ spl6_8
    | ~ spl6_31
    | spl6_27 ),
    inference(avatar_split_clause,[],[f273,f259,f275,f146])).

fof(f273,plain,
    ( ~ m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_27 ),
    inference(resolution,[],[f260,f82])).

fof(f260,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f259])).

fof(f245,plain,
    ( ~ spl6_8
    | ~ spl6_6
    | spl6_21 ),
    inference(avatar_split_clause,[],[f243,f227,f138,f146])).

fof(f243,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_21 ),
    inference(resolution,[],[f228,f82])).

fof(f228,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f227])).

fof(f191,plain,
    ( ~ spl6_8
    | spl6_14
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f179,f172,f189,f146])).

fof(f172,plain,
    ( spl6_11
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f179,plain,
    ( k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f173,f80])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f172])).

fof(f187,plain,
    ( spl6_13
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f178,f172,f138,f185])).

fof(f178,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(resolution,[],[f173,f139])).

fof(f174,plain,
    ( spl6_10
    | ~ spl6_8
    | spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f166,f150,f172,f146,f154])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))
        | v2_struct_0(sK0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f162,f151])).

fof(f151,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f161,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f161,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f160,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f157,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f82,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK4(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK4(X0,X1,X2)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK4(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK4(X0,X1,X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f156,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f67,f154])).

fof(f67,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f56,f55,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                    & m1_subset_1(X3,u1_struct_0(X2)) )
                & r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tmap_1(X2,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X3)
                & m1_subset_1(X3,u1_struct_0(X2)) )
            & r1_tsep_1(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tmap_1(X2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X3)
              & m1_subset_1(X3,u1_struct_0(X2)) )
          & r1_tsep_1(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tmap_1(X2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X3)
            & m1_subset_1(X3,u1_struct_0(X2)) )
        & r1_tsep_1(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3)
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_tsep_1(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
               => ( r1_tsep_1(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
             => ( r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_tmap_1)).

fof(f152,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f68,f150])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f148,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f69,f146])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f140,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f71,f138])).

fof(f71,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f136,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f72,f134])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f132,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f73,f130])).

fof(f73,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f128,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f74,f126])).

fof(f74,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f124,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f75,f122])).

fof(f75,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f57])).

fof(f120,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f76,f118])).

fof(f76,plain,(
    ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22087)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (22078)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (22079)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (22075)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (22073)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (22086)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (22077)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (22076)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (22074)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (22088)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (22074)Refutation not found, incomplete strategy% (22074)------------------------------
% 0.22/0.52  % (22074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22074)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22074)Memory used [KB]: 10618
% 0.22/0.52  % (22074)Time elapsed: 0.097 s
% 0.22/0.52  % (22074)------------------------------
% 0.22/0.52  % (22074)------------------------------
% 0.22/0.52  % (22082)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (22086)Refutation not found, incomplete strategy% (22086)------------------------------
% 0.22/0.52  % (22086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22093)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (22085)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (22080)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (22092)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (22090)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (22093)Refutation not found, incomplete strategy% (22093)------------------------------
% 0.22/0.52  % (22093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22093)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22093)Memory used [KB]: 10618
% 0.22/0.52  % (22093)Time elapsed: 0.103 s
% 0.22/0.52  % (22093)------------------------------
% 0.22/0.52  % (22093)------------------------------
% 0.22/0.52  % (22081)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (22084)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (22085)Refutation not found, incomplete strategy% (22085)------------------------------
% 0.22/0.53  % (22085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22085)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22085)Memory used [KB]: 6396
% 0.22/0.53  % (22085)Time elapsed: 0.113 s
% 0.22/0.53  % (22085)------------------------------
% 0.22/0.53  % (22085)------------------------------
% 0.22/0.53  % (22083)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.53  % (22091)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (22089)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.53  % (22083)Refutation not found, incomplete strategy% (22083)------------------------------
% 0.22/0.53  % (22083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22086)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22086)Memory used [KB]: 2046
% 0.22/0.53  % (22086)Time elapsed: 0.097 s
% 0.22/0.53  % (22086)------------------------------
% 0.22/0.53  % (22086)------------------------------
% 0.22/0.55  % (22083)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (22083)Memory used [KB]: 6396
% 0.22/0.55  % (22083)Time elapsed: 0.115 s
% 0.22/0.55  % (22083)------------------------------
% 0.22/0.55  % (22083)------------------------------
% 1.52/0.56  % (22073)Refutation not found, incomplete strategy% (22073)------------------------------
% 1.52/0.56  % (22073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (22073)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (22073)Memory used [KB]: 7419
% 1.52/0.56  % (22073)Time elapsed: 0.132 s
% 1.52/0.56  % (22073)------------------------------
% 1.52/0.56  % (22073)------------------------------
% 1.66/0.60  % (22079)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.62  % SZS output start Proof for theBenchmark
% 1.66/0.62  fof(f3210,plain,(
% 1.66/0.62    $false),
% 1.66/0.62    inference(avatar_sat_refutation,[],[f120,f124,f128,f132,f136,f140,f148,f152,f156,f174,f187,f191,f245,f277,f279,f325,f330,f348,f353,f442,f454,f594,f607,f614,f647,f1272,f1353,f1365,f1405,f1416,f1421,f1427,f1477,f1481,f1870,f2463,f2640,f2645,f2647,f2679,f2721,f3209])).
% 1.66/0.62  fof(f3209,plain,(
% 1.66/0.62    ~spl6_6 | spl6_10 | ~spl6_9 | ~spl6_8 | spl6_306 | ~spl6_303),
% 1.66/0.62    inference(avatar_split_clause,[],[f3207,f2677,f2719,f146,f150,f154,f138])).
% 1.66/0.62  fof(f138,plain,(
% 1.66/0.62    spl6_6 <=> m1_pre_topc(sK1,sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.66/0.62  fof(f154,plain,(
% 1.66/0.62    spl6_10 <=> v2_struct_0(sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.66/0.62  fof(f150,plain,(
% 1.66/0.62    spl6_9 <=> v2_pre_topc(sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.66/0.62  fof(f146,plain,(
% 1.66/0.62    spl6_8 <=> l1_pre_topc(sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.66/0.62  fof(f2719,plain,(
% 1.66/0.62    spl6_306 <=> r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK3)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_306])])).
% 1.66/0.62  fof(f2677,plain,(
% 1.66/0.62    spl6_303 <=> r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),sK3)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_303])])).
% 1.66/0.62  fof(f3207,plain,(
% 1.66/0.62    r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | ~spl6_303),
% 1.66/0.62    inference(superposition,[],[f2678,f242])).
% 1.66/0.62  fof(f242,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)) )),
% 1.66/0.62    inference(duplicate_literal_removal,[],[f241])).
% 1.66/0.62  fof(f241,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.66/0.62    inference(resolution,[],[f92,f82])).
% 1.66/0.62  fof(f82,plain,(
% 1.66/0.62    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f27])).
% 1.66/0.62  fof(f27,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f17])).
% 1.66/0.62  fof(f17,axiom,(
% 1.66/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.66/0.62  fof(f92,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f35])).
% 1.66/0.62  fof(f35,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f34])).
% 1.66/0.62  fof(f34,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f6])).
% 1.66/0.62  fof(f6,axiom,(
% 1.66/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).
% 1.66/0.62  fof(f2678,plain,(
% 1.66/0.62    r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),sK3) | ~spl6_303),
% 1.66/0.62    inference(avatar_component_clause,[],[f2677])).
% 1.66/0.62  fof(f2721,plain,(
% 1.66/0.62    ~spl6_306 | spl6_1 | ~spl6_154),
% 1.66/0.62    inference(avatar_split_clause,[],[f1366,f1363,f118,f2719])).
% 1.66/0.62  fof(f118,plain,(
% 1.66/0.62    spl6_1 <=> r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.66/0.62  fof(f1363,plain,(
% 1.66/0.62    spl6_154 <=> k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_154])])).
% 1.66/0.62  fof(f1366,plain,(
% 1.66/0.62    ~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK2),sK3) | (spl6_1 | ~spl6_154)),
% 1.66/0.62    inference(superposition,[],[f119,f1364])).
% 1.66/0.62  fof(f1364,plain,(
% 1.66/0.62    k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~spl6_154),
% 1.66/0.62    inference(avatar_component_clause,[],[f1363])).
% 1.66/0.62  fof(f119,plain,(
% 1.66/0.62    ~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) | spl6_1),
% 1.66/0.62    inference(avatar_component_clause,[],[f118])).
% 1.66/0.62  fof(f2679,plain,(
% 1.66/0.62    ~spl6_40 | ~spl6_21 | spl6_303 | ~spl6_3 | ~spl6_13 | ~spl6_161),
% 1.66/0.62    inference(avatar_split_clause,[],[f1433,f1425,f185,f126,f2677,f227,f319])).
% 1.66/0.62  fof(f319,plain,(
% 1.66/0.62    spl6_40 <=> l1_pre_topc(sK1)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.66/0.62  fof(f227,plain,(
% 1.66/0.62    spl6_21 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.66/0.62  fof(f126,plain,(
% 1.66/0.62    spl6_3 <=> r1_tsep_1(sK1,sK2)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.66/0.62  fof(f185,plain,(
% 1.66/0.62    spl6_13 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.66/0.62  fof(f1425,plain,(
% 1.66/0.62    spl6_161 <=> ! [X1] : (r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X1)),k7_tmap_1(sK0,u1_struct_0(X1)),sK2),sK3) | ~l1_struct_0(X1) | ~r1_tsep_1(X1,sK2) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).
% 1.66/0.62  fof(f1433,plain,(
% 1.66/0.62    r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),sK3) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK1) | (~spl6_3 | ~spl6_13 | ~spl6_161)),
% 1.66/0.62    inference(forward_demodulation,[],[f1431,f186])).
% 1.66/0.62  fof(f186,plain,(
% 1.66/0.62    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_13),
% 1.66/0.62    inference(avatar_component_clause,[],[f185])).
% 1.66/0.62  fof(f1431,plain,(
% 1.66/0.62    r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(sK1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK2),sK3) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK1) | (~spl6_3 | ~spl6_161)),
% 1.66/0.62    inference(resolution,[],[f1430,f127])).
% 1.66/0.62  fof(f127,plain,(
% 1.66/0.62    r1_tsep_1(sK1,sK2) | ~spl6_3),
% 1.66/0.62    inference(avatar_component_clause,[],[f126])).
% 1.66/0.62  fof(f1430,plain,(
% 1.66/0.62    ( ! [X0] : (~r1_tsep_1(X0,sK2) | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X0)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X0)),k7_tmap_1(sK0,u1_struct_0(X0)),sK2),sK3) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(X0)) ) | ~spl6_161),
% 1.66/0.62    inference(resolution,[],[f1426,f79])).
% 1.66/0.62  fof(f79,plain,(
% 1.66/0.62    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f24])).
% 1.66/0.62  fof(f24,plain,(
% 1.66/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f2])).
% 1.66/0.62  fof(f2,axiom,(
% 1.66/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.66/0.62  fof(f1426,plain,(
% 1.66/0.62    ( ! [X1] : (~l1_struct_0(X1) | r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X1)),k7_tmap_1(sK0,u1_struct_0(X1)),sK2),sK3) | ~r1_tsep_1(X1,sK2) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_161),
% 1.66/0.62    inference(avatar_component_clause,[],[f1425])).
% 1.66/0.62  fof(f2647,plain,(
% 1.66/0.62    ~spl6_8 | spl6_300),
% 1.66/0.62    inference(avatar_split_clause,[],[f2646,f2643,f146])).
% 1.66/0.62  fof(f2643,plain,(
% 1.66/0.62    spl6_300 <=> l1_struct_0(sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_300])])).
% 1.66/0.62  fof(f2646,plain,(
% 1.66/0.62    ~l1_pre_topc(sK0) | spl6_300),
% 1.66/0.62    inference(resolution,[],[f2644,f79])).
% 1.66/0.62  fof(f2644,plain,(
% 1.66/0.62    ~l1_struct_0(sK0) | spl6_300),
% 1.66/0.62    inference(avatar_component_clause,[],[f2643])).
% 1.66/0.62  fof(f2645,plain,(
% 1.66/0.62    spl6_10 | ~spl6_300 | ~spl6_130),
% 1.66/0.62    inference(avatar_split_clause,[],[f2641,f1079,f2643,f154])).
% 1.66/0.62  fof(f1079,plain,(
% 1.66/0.62    spl6_130 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).
% 1.66/0.62  fof(f2641,plain,(
% 1.66/0.62    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_130),
% 1.66/0.62    inference(resolution,[],[f2459,f83])).
% 1.66/0.62  fof(f83,plain,(
% 1.66/0.62    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f29])).
% 1.66/0.62  fof(f29,plain,(
% 1.66/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f28])).
% 1.66/0.62  fof(f28,plain,(
% 1.66/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f4])).
% 1.66/0.62  fof(f4,axiom,(
% 1.66/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.66/0.62  fof(f2459,plain,(
% 1.66/0.62    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_130),
% 1.66/0.62    inference(avatar_component_clause,[],[f1079])).
% 1.66/0.62  fof(f2640,plain,(
% 1.66/0.62    ~spl6_74 | ~spl6_79 | ~spl6_59 | ~spl6_275),
% 1.66/0.62    inference(avatar_split_clause,[],[f2639,f2461,f452,f645,f605])).
% 1.66/0.62  fof(f605,plain,(
% 1.66/0.62    spl6_74 <=> v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 1.66/0.62  fof(f645,plain,(
% 1.66/0.62    spl6_79 <=> m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 1.66/0.62  fof(f452,plain,(
% 1.66/0.62    spl6_59 <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 1.66/0.62  fof(f2461,plain,(
% 1.66/0.62    spl6_275 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_275])])).
% 1.66/0.62  fof(f2639,plain,(
% 1.66/0.62    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl6_59 | ~spl6_275)),
% 1.66/0.62    inference(resolution,[],[f2462,f453])).
% 1.66/0.62  fof(f453,plain,(
% 1.66/0.62    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~spl6_59),
% 1.66/0.62    inference(avatar_component_clause,[],[f452])).
% 1.66/0.62  fof(f2462,plain,(
% 1.66/0.62    ( ! [X0] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0))) ) | ~spl6_275),
% 1.66/0.62    inference(avatar_component_clause,[],[f2461])).
% 1.66/0.62  fof(f2463,plain,(
% 1.66/0.62    spl6_130 | ~spl6_59 | ~spl6_74 | ~spl6_79 | spl6_275 | spl6_148),
% 1.66/0.62    inference(avatar_split_clause,[],[f2458,f1318,f2461,f645,f605,f452,f1079])).
% 1.66/0.62  fof(f1318,plain,(
% 1.66/0.62    spl6_148 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).
% 1.66/0.62  fof(f2458,plain,(
% 1.66/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))) ) | spl6_148),
% 1.66/0.62    inference(duplicate_literal_removal,[],[f2457])).
% 1.66/0.62  fof(f2457,plain,(
% 1.66/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | spl6_148),
% 1.66/0.62    inference(resolution,[],[f1855,f111])).
% 1.66/0.62  fof(f111,plain,(
% 1.66/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f52])).
% 1.66/0.62  fof(f52,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.66/0.62    inference(flattening,[],[f51])).
% 1.66/0.62  fof(f51,plain,(
% 1.66/0.62    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.66/0.62    inference(ennf_transformation,[],[f5])).
% 1.66/0.62  fof(f5,axiom,(
% 1.66/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).
% 1.66/0.62  fof(f1855,plain,(
% 1.66/0.62    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | spl6_148),
% 1.66/0.62    inference(avatar_component_clause,[],[f1318])).
% 1.66/0.62  fof(f1870,plain,(
% 1.66/0.62    ~spl6_59 | spl6_154 | ~spl6_79 | ~spl6_74 | ~spl6_148 | ~spl6_6 | ~spl6_43 | ~spl6_152 | ~spl6_170 | ~spl6_171),
% 1.66/0.62    inference(avatar_split_clause,[],[f1869,f1479,f1475,f1351,f346,f138,f1318,f605,f645,f1363,f452])).
% 1.66/0.62  fof(f346,plain,(
% 1.66/0.62    spl6_43 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 1.66/0.62  fof(f1351,plain,(
% 1.66/0.62    spl6_152 <=> ! [X5,X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X4,X5))),X5,k7_tmap_1(sK0,sK5(sK0,X4,X5))) | k9_tmap_1(sK0,X4) = X5 | ~m1_pre_topc(X4,sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))))))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_152])])).
% 1.66/0.62  fof(f1475,plain,(
% 1.66/0.62    spl6_170 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_170])])).
% 1.66/0.62  fof(f1479,plain,(
% 1.66/0.62    spl6_171 <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_171])])).
% 1.66/0.62  fof(f1869,plain,(
% 1.66/0.62    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | (~spl6_6 | ~spl6_43 | ~spl6_152 | ~spl6_170 | ~spl6_171)),
% 1.66/0.62    inference(forward_demodulation,[],[f1851,f1476])).
% 1.66/0.62  fof(f1476,plain,(
% 1.66/0.62    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))) | ~spl6_170),
% 1.66/0.62    inference(avatar_component_clause,[],[f1475])).
% 1.66/0.62  fof(f1851,plain,(
% 1.66/0.62    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | (~spl6_6 | ~spl6_43 | ~spl6_152 | ~spl6_171)),
% 1.66/0.62    inference(superposition,[],[f1650,f1480])).
% 1.66/0.62  fof(f1480,plain,(
% 1.66/0.62    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))) | ~spl6_171),
% 1.66/0.62    inference(avatar_component_clause,[],[f1479])).
% 1.66/0.62  fof(f1650,plain,(
% 1.66/0.62    ( ! [X1] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,X1))),X1,k7_tmap_1(sK0,sK5(sK0,sK1,X1))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | k9_tmap_1(sK0,sK1) = X1 | ~v1_funct_1(X1)) ) | (~spl6_6 | ~spl6_43 | ~spl6_152)),
% 1.66/0.62    inference(forward_demodulation,[],[f1649,f347])).
% 1.66/0.62  fof(f347,plain,(
% 1.66/0.62    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl6_43),
% 1.66/0.62    inference(avatar_component_clause,[],[f346])).
% 1.66/0.62  fof(f1649,plain,(
% 1.66/0.62    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,X1))),X1,k7_tmap_1(sK0,sK5(sK0,sK1,X1))) | k9_tmap_1(sK0,sK1) = X1 | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))) ) | (~spl6_6 | ~spl6_43 | ~spl6_152)),
% 1.66/0.62    inference(forward_demodulation,[],[f1648,f347])).
% 1.66/0.62  fof(f1648,plain,(
% 1.66/0.62    ( ! [X1] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,X1))),X1,k7_tmap_1(sK0,sK5(sK0,sK1,X1))) | k9_tmap_1(sK0,sK1) = X1 | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))) ) | (~spl6_6 | ~spl6_43 | ~spl6_152)),
% 1.66/0.62    inference(forward_demodulation,[],[f1642,f347])).
% 1.66/0.62  fof(f1642,plain,(
% 1.66/0.62    ( ! [X1] : (k9_tmap_1(sK0,sK1) = X1 | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,X1))),X1,k7_tmap_1(sK0,sK5(sK0,sK1,X1))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))) ) | (~spl6_6 | ~spl6_152)),
% 1.66/0.62    inference(resolution,[],[f1352,f139])).
% 1.66/0.62  fof(f139,plain,(
% 1.66/0.62    m1_pre_topc(sK1,sK0) | ~spl6_6),
% 1.66/0.62    inference(avatar_component_clause,[],[f138])).
% 1.66/0.62  fof(f1352,plain,(
% 1.66/0.62    ( ! [X4,X5] : (~m1_pre_topc(X4,sK0) | k9_tmap_1(sK0,X4) = X5 | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X4,X5))),X5,k7_tmap_1(sK0,sK5(sK0,X4,X5))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))))) ) | ~spl6_152),
% 1.66/0.62    inference(avatar_component_clause,[],[f1351])).
% 1.66/0.62  fof(f1481,plain,(
% 1.66/0.62    spl6_10 | ~spl6_9 | ~spl6_8 | spl6_171 | ~spl6_153),
% 1.66/0.62    inference(avatar_split_clause,[],[f1447,f1360,f1479,f146,f150,f154])).
% 1.66/0.62  fof(f1360,plain,(
% 1.66/0.62    spl6_153 <=> m1_subset_1(sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_153])])).
% 1.66/0.62  fof(f1447,plain,(
% 1.66/0.62    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_153),
% 1.66/0.62    inference(resolution,[],[f1361,f92])).
% 1.66/0.62  fof(f1361,plain,(
% 1.66/0.62    m1_subset_1(sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_153),
% 1.66/0.62    inference(avatar_component_clause,[],[f1360])).
% 1.66/0.62  fof(f1477,plain,(
% 1.66/0.62    spl6_10 | ~spl6_9 | ~spl6_8 | spl6_170 | ~spl6_153),
% 1.66/0.62    inference(avatar_split_clause,[],[f1446,f1360,f1475,f146,f150,f154])).
% 1.66/0.62  fof(f1446,plain,(
% 1.66/0.62    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_153),
% 1.66/0.62    inference(resolution,[],[f1361,f93])).
% 1.66/0.62  fof(f93,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f37])).
% 1.66/0.62  fof(f37,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f36])).
% 1.66/0.62  fof(f36,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f14])).
% 1.66/0.62  fof(f14,axiom,(
% 1.66/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.66/0.62  fof(f1427,plain,(
% 1.66/0.62    ~spl6_159 | spl6_161 | ~spl6_158),
% 1.66/0.62    inference(avatar_split_clause,[],[f1423,f1403,f1425,f1409])).
% 1.66/0.62  fof(f1409,plain,(
% 1.66/0.62    spl6_159 <=> l1_struct_0(sK2)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_159])])).
% 1.66/0.62  fof(f1403,plain,(
% 1.66/0.62    spl6_158 <=> ! [X0] : (~r1_xboole_0(u1_struct_0(sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tmap_1(sK2,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK3))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_158])])).
% 1.66/0.62  fof(f1423,plain,(
% 1.66/0.62    ( ! [X1] : (r1_tmap_1(sK2,k6_tmap_1(sK0,u1_struct_0(X1)),k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(X1)),k7_tmap_1(sK0,u1_struct_0(X1)),sK2),sK3) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tsep_1(X1,sK2) | ~l1_struct_0(sK2) | ~l1_struct_0(X1)) ) | ~spl6_158),
% 1.66/0.62    inference(resolution,[],[f1407,f77])).
% 1.66/0.62  fof(f77,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f58])).
% 1.66/0.62  fof(f58,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.66/0.62    inference(nnf_transformation,[],[f23])).
% 1.66/0.62  fof(f23,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f9])).
% 1.66/0.62  fof(f9,axiom,(
% 1.66/0.62    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 1.66/0.62  fof(f1407,plain,(
% 1.66/0.62    ( ! [X1] : (~r1_xboole_0(X1,u1_struct_0(sK2)) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_158),
% 1.66/0.62    inference(resolution,[],[f1404,f98])).
% 1.66/0.62  fof(f98,plain,(
% 1.66/0.62    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f42])).
% 1.66/0.62  fof(f42,plain,(
% 1.66/0.62    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.66/0.62    inference(ennf_transformation,[],[f1])).
% 1.66/0.62  fof(f1,axiom,(
% 1.66/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.66/0.62  fof(f1404,plain,(
% 1.66/0.62    ( ! [X0] : (~r1_xboole_0(u1_struct_0(sK2),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tmap_1(sK2,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK3)) ) | ~spl6_158),
% 1.66/0.62    inference(avatar_component_clause,[],[f1403])).
% 1.66/0.62  fof(f1421,plain,(
% 1.66/0.62    ~spl6_8 | ~spl6_4 | spl6_37),
% 1.66/0.62    inference(avatar_split_clause,[],[f1418,f309,f130,f146])).
% 1.66/0.62  fof(f130,plain,(
% 1.66/0.62    spl6_4 <=> m1_pre_topc(sK2,sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.66/0.62  fof(f309,plain,(
% 1.66/0.62    spl6_37 <=> l1_pre_topc(sK2)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.66/0.62  fof(f1418,plain,(
% 1.66/0.62    ~l1_pre_topc(sK0) | (~spl6_4 | spl6_37)),
% 1.66/0.62    inference(resolution,[],[f1417,f131])).
% 1.66/0.62  fof(f131,plain,(
% 1.66/0.62    m1_pre_topc(sK2,sK0) | ~spl6_4),
% 1.66/0.62    inference(avatar_component_clause,[],[f130])).
% 1.66/0.62  fof(f1417,plain,(
% 1.66/0.62    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl6_37),
% 1.66/0.62    inference(resolution,[],[f310,f81])).
% 1.66/0.62  fof(f81,plain,(
% 1.66/0.62    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f26])).
% 1.66/0.62  fof(f26,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f3])).
% 1.66/0.62  fof(f3,axiom,(
% 1.66/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.66/0.62  fof(f310,plain,(
% 1.66/0.62    ~l1_pre_topc(sK2) | spl6_37),
% 1.66/0.62    inference(avatar_component_clause,[],[f309])).
% 1.66/0.62  fof(f1416,plain,(
% 1.66/0.62    ~spl6_37 | spl6_159),
% 1.66/0.62    inference(avatar_split_clause,[],[f1415,f1409,f309])).
% 1.66/0.62  fof(f1415,plain,(
% 1.66/0.62    ~l1_pre_topc(sK2) | spl6_159),
% 1.66/0.62    inference(resolution,[],[f1410,f79])).
% 1.66/0.62  fof(f1410,plain,(
% 1.66/0.62    ~l1_struct_0(sK2) | spl6_159),
% 1.66/0.62    inference(avatar_component_clause,[],[f1409])).
% 1.66/0.62  fof(f1405,plain,(
% 1.66/0.62    spl6_10 | ~spl6_9 | ~spl6_8 | spl6_158 | ~spl6_2 | ~spl6_4 | spl6_5),
% 1.66/0.62    inference(avatar_split_clause,[],[f1399,f134,f130,f122,f1403,f146,f150,f154])).
% 1.66/0.62  fof(f122,plain,(
% 1.66/0.62    spl6_2 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.66/0.62  fof(f134,plain,(
% 1.66/0.62    spl6_5 <=> v2_struct_0(sK2)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.66/0.62  fof(f1399,plain,(
% 1.66/0.62    ( ! [X0] : (~r1_xboole_0(u1_struct_0(sK2),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_4 | spl6_5)),
% 1.66/0.62    inference(resolution,[],[f1398,f131])).
% 1.66/0.62  fof(f1398,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~m1_pre_topc(sK2,X1) | ~r1_xboole_0(u1_struct_0(sK2),X0) | r1_tmap_1(sK2,k6_tmap_1(X1,X0),k2_tmap_1(X1,k6_tmap_1(X1,X0),k7_tmap_1(X1,X0),sK2),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl6_2 | spl6_5)),
% 1.66/0.62    inference(resolution,[],[f1038,f123])).
% 1.66/0.62  fof(f123,plain,(
% 1.66/0.62    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl6_2),
% 1.66/0.62    inference(avatar_component_clause,[],[f122])).
% 1.66/0.62  fof(f1038,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_xboole_0(u1_struct_0(sK2),X1) | ~m1_pre_topc(sK2,X2) | r1_tmap_1(sK2,k6_tmap_1(X2,X1),k2_tmap_1(X2,k6_tmap_1(X2,X1),k7_tmap_1(X2,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | spl6_5),
% 1.66/0.62    inference(resolution,[],[f95,f135])).
% 1.66/0.62  fof(f135,plain,(
% 1.66/0.62    ~v2_struct_0(sK2) | spl6_5),
% 1.66/0.62    inference(avatar_component_clause,[],[f134])).
% 1.66/0.62  fof(f95,plain,(
% 1.66/0.62    ( ! [X2,X0,X3,X1] : (v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f39])).
% 1.66/0.62  fof(f39,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f38])).
% 1.66/0.62  fof(f38,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f15])).
% 1.66/0.62  fof(f15,axiom,(
% 1.66/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).
% 1.66/0.62  fof(f1365,plain,(
% 1.66/0.62    ~spl6_79 | spl6_153 | spl6_154 | ~spl6_74 | ~spl6_6 | ~spl6_43 | ~spl6_59 | ~spl6_144),
% 1.66/0.62    inference(avatar_split_clause,[],[f1358,f1270,f452,f346,f138,f605,f1363,f1360,f645])).
% 1.66/0.62  fof(f1270,plain,(
% 1.66/0.62    spl6_144 <=> ! [X5,X4] : (m1_subset_1(sK5(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0))) | k9_tmap_1(sK0,X4) = X5 | ~m1_pre_topc(X4,sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))))))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).
% 1.66/0.62  fof(f1358,plain,(
% 1.66/0.62    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | m1_subset_1(sK5(sK0,sK1,k6_partfun1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (~spl6_6 | ~spl6_43 | ~spl6_59 | ~spl6_144)),
% 1.66/0.62    inference(resolution,[],[f1291,f453])).
% 1.66/0.62  fof(f1291,plain,(
% 1.66/0.62    ( ! [X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = X1 | m1_subset_1(sK5(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))) ) | (~spl6_6 | ~spl6_43 | ~spl6_144)),
% 1.66/0.62    inference(forward_demodulation,[],[f1290,f347])).
% 1.66/0.62  fof(f1290,plain,(
% 1.66/0.62    ( ! [X1] : (~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(sK0)) | k9_tmap_1(sK0,sK1) = X1 | m1_subset_1(sK5(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))) ) | (~spl6_6 | ~spl6_43 | ~spl6_144)),
% 1.66/0.62    inference(forward_demodulation,[],[f1286,f347])).
% 1.66/0.62  fof(f1286,plain,(
% 1.66/0.62    ( ! [X1] : (k9_tmap_1(sK0,sK1) = X1 | m1_subset_1(sK5(sK0,sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))) ) | (~spl6_6 | ~spl6_144)),
% 1.66/0.62    inference(resolution,[],[f1271,f139])).
% 1.66/0.62  fof(f1271,plain,(
% 1.66/0.62    ( ! [X4,X5] : (~m1_pre_topc(X4,sK0) | k9_tmap_1(sK0,X4) = X5 | m1_subset_1(sK5(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)))))) ) | ~spl6_144),
% 1.66/0.62    inference(avatar_component_clause,[],[f1270])).
% 1.66/0.62  fof(f1353,plain,(
% 1.66/0.62    ~spl6_9 | ~spl6_8 | spl6_152 | spl6_10),
% 1.66/0.62    inference(avatar_split_clause,[],[f1349,f154,f1351,f146,f150])).
% 1.66/0.62  fof(f1349,plain,(
% 1.66/0.62    ( ! [X4,X5] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK5(sK0,X4,X5))),X5,k7_tmap_1(sK0,sK5(sK0,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))))) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))) | ~v1_funct_1(X5) | ~m1_pre_topc(X4,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k9_tmap_1(sK0,X4) = X5) ) | spl6_10),
% 1.66/0.62    inference(resolution,[],[f91,f155])).
% 1.66/0.62  fof(f155,plain,(
% 1.66/0.62    ~v2_struct_0(sK0) | spl6_10),
% 1.66/0.62    inference(avatar_component_clause,[],[f154])).
% 1.66/0.62  fof(f91,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k9_tmap_1(X0,X1) = X2) )),
% 1.66/0.62    inference(cnf_transformation,[],[f66])).
% 1.66/0.62  fof(f66,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) & u1_struct_0(X1) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f64,f65])).
% 1.66/0.62  fof(f65,plain,(
% 1.66/0.62    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) & u1_struct_0(X1) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f64,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(rectify,[],[f63])).
% 1.66/0.62  fof(f63,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(nnf_transformation,[],[f33])).
% 1.66/0.62  fof(f33,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f32])).
% 1.66/0.62  fof(f32,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f8])).
% 1.66/0.62  fof(f8,axiom,(
% 1.66/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).
% 1.66/0.62  fof(f1272,plain,(
% 1.66/0.62    ~spl6_9 | ~spl6_8 | spl6_144 | spl6_10),
% 1.66/0.62    inference(avatar_split_clause,[],[f1268,f154,f1270,f146,f150])).
% 1.66/0.62  fof(f1268,plain,(
% 1.66/0.62    ( ! [X4,X5] : (m1_subset_1(sK5(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))))) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X4))) | ~v1_funct_1(X5) | ~m1_pre_topc(X4,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k9_tmap_1(sK0,X4) = X5) ) | spl6_10),
% 1.66/0.62    inference(resolution,[],[f89,f155])).
% 1.66/0.62  fof(f89,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (v2_struct_0(X0) | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k9_tmap_1(X0,X1) = X2) )),
% 1.66/0.62    inference(cnf_transformation,[],[f66])).
% 1.66/0.62  fof(f647,plain,(
% 1.66/0.62    spl6_79 | ~spl6_14 | ~spl6_27 | ~spl6_44 | ~spl6_57 | ~spl6_75),
% 1.66/0.62    inference(avatar_split_clause,[],[f643,f612,f440,f351,f259,f189,f645])).
% 1.66/0.62  fof(f189,plain,(
% 1.66/0.62    spl6_14 <=> k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.66/0.62  fof(f259,plain,(
% 1.66/0.62    spl6_27 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.66/0.62  fof(f351,plain,(
% 1.66/0.62    spl6_44 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 1.66/0.62  fof(f440,plain,(
% 1.66/0.62    spl6_57 <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 1.66/0.62  fof(f612,plain,(
% 1.66/0.62    spl6_75 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2))))))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).
% 1.66/0.62  fof(f643,plain,(
% 1.66/0.62    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (~spl6_14 | ~spl6_27 | ~spl6_44 | ~spl6_57 | ~spl6_75)),
% 1.66/0.62    inference(forward_demodulation,[],[f642,f441])).
% 1.66/0.62  fof(f441,plain,(
% 1.66/0.62    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0)) | ~spl6_57),
% 1.66/0.62    inference(avatar_component_clause,[],[f440])).
% 1.66/0.62  fof(f642,plain,(
% 1.66/0.62    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (~spl6_14 | ~spl6_27 | ~spl6_44 | ~spl6_75)),
% 1.66/0.62    inference(forward_demodulation,[],[f641,f352])).
% 1.66/0.62  fof(f352,plain,(
% 1.66/0.62    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) | ~spl6_44),
% 1.66/0.62    inference(avatar_component_clause,[],[f351])).
% 1.66/0.62  fof(f641,plain,(
% 1.66/0.62    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))))) | (~spl6_14 | ~spl6_27 | ~spl6_75)),
% 1.66/0.62    inference(forward_demodulation,[],[f636,f190])).
% 1.66/0.62  fof(f190,plain,(
% 1.66/0.62    k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | ~spl6_14),
% 1.66/0.62    inference(avatar_component_clause,[],[f189])).
% 1.66/0.62  fof(f636,plain,(
% 1.66/0.62    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))))) | (~spl6_27 | ~spl6_75)),
% 1.66/0.62    inference(resolution,[],[f613,f434])).
% 1.66/0.62  fof(f434,plain,(
% 1.66/0.62    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_27),
% 1.66/0.62    inference(avatar_component_clause,[],[f259])).
% 1.66/0.62  fof(f613,plain,(
% 1.66/0.62    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2)))))) ) | ~spl6_75),
% 1.66/0.62    inference(avatar_component_clause,[],[f612])).
% 1.66/0.62  fof(f614,plain,(
% 1.66/0.62    ~spl6_9 | ~spl6_8 | spl6_75 | spl6_10),
% 1.66/0.62    inference(avatar_split_clause,[],[f610,f154,f612,f146,f150])).
% 1.66/0.62  fof(f610,plain,(
% 1.66/0.62    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(k7_tmap_1(sK0,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2)))))) ) | spl6_10),
% 1.66/0.62    inference(resolution,[],[f110,f155])).
% 1.66/0.62  fof(f110,plain,(
% 1.66/0.62    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f50])).
% 1.66/0.62  fof(f50,plain,(
% 1.66/0.62    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f49])).
% 1.66/0.62  fof(f49,plain,(
% 1.66/0.62    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f11])).
% 1.66/0.62  fof(f11,axiom,(
% 1.66/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.66/0.62  fof(f607,plain,(
% 1.66/0.62    spl6_74 | ~spl6_14 | ~spl6_27 | ~spl6_44 | ~spl6_57 | ~spl6_72),
% 1.66/0.62    inference(avatar_split_clause,[],[f603,f592,f440,f351,f259,f189,f605])).
% 1.66/0.62  fof(f592,plain,(
% 1.66/0.62    spl6_72 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X2),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2))))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 1.66/0.62  fof(f603,plain,(
% 1.66/0.62    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl6_14 | ~spl6_27 | ~spl6_44 | ~spl6_57 | ~spl6_72)),
% 1.66/0.62    inference(forward_demodulation,[],[f602,f441])).
% 1.66/0.62  fof(f602,plain,(
% 1.66/0.62    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl6_14 | ~spl6_27 | ~spl6_44 | ~spl6_72)),
% 1.66/0.62    inference(forward_demodulation,[],[f601,f352])).
% 1.66/0.62  fof(f601,plain,(
% 1.66/0.62    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK0))) | (~spl6_14 | ~spl6_27 | ~spl6_72)),
% 1.66/0.62    inference(forward_demodulation,[],[f596,f190])).
% 1.66/0.62  fof(f596,plain,(
% 1.66/0.62    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))) | (~spl6_27 | ~spl6_72)),
% 1.66/0.62    inference(resolution,[],[f593,f434])).
% 1.66/0.62  fof(f593,plain,(
% 1.66/0.62    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X2),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2)))) ) | ~spl6_72),
% 1.66/0.62    inference(avatar_component_clause,[],[f592])).
% 1.66/0.62  fof(f594,plain,(
% 1.66/0.62    ~spl6_9 | ~spl6_8 | spl6_72 | spl6_10),
% 1.66/0.62    inference(avatar_split_clause,[],[f590,f154,f592,f146,f150])).
% 1.66/0.62  fof(f590,plain,(
% 1.66/0.62    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_funct_2(k7_tmap_1(sK0,X2),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X2)))) ) | spl6_10),
% 1.66/0.62    inference(resolution,[],[f109,f155])).
% 1.66/0.62  fof(f109,plain,(
% 1.66/0.62    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))) )),
% 1.66/0.62    inference(cnf_transformation,[],[f50])).
% 1.66/0.62  fof(f454,plain,(
% 1.66/0.62    spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_27 | spl6_59 | ~spl6_57),
% 1.66/0.62    inference(avatar_split_clause,[],[f450,f440,f452,f259,f146,f150,f154])).
% 1.66/0.62  fof(f450,plain,(
% 1.66/0.62    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_57),
% 1.66/0.62    inference(superposition,[],[f108,f441])).
% 1.66/0.62  fof(f108,plain,(
% 1.66/0.62    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f50])).
% 1.66/0.62  fof(f442,plain,(
% 1.66/0.62    spl6_10 | ~spl6_9 | ~spl6_8 | spl6_57 | ~spl6_27),
% 1.66/0.62    inference(avatar_split_clause,[],[f437,f259,f440,f146,f150,f154])).
% 1.66/0.62  fof(f437,plain,(
% 1.66/0.62    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_27),
% 1.66/0.62    inference(resolution,[],[f434,f92])).
% 1.66/0.62  fof(f353,plain,(
% 1.66/0.62    ~spl6_8 | spl6_44 | ~spl6_14 | ~spl6_41),
% 1.66/0.62    inference(avatar_split_clause,[],[f349,f323,f189,f351,f146])).
% 1.66/0.62  fof(f323,plain,(
% 1.66/0.62    spl6_41 <=> ! [X2] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X2))) | ~m1_pre_topc(X2,sK0))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 1.66/0.62  fof(f349,plain,(
% 1.66/0.62    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK0)) | ~l1_pre_topc(sK0) | (~spl6_14 | ~spl6_41)),
% 1.66/0.62    inference(forward_demodulation,[],[f338,f190])).
% 1.66/0.62  fof(f338,plain,(
% 1.66/0.62    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl6_41),
% 1.66/0.62    inference(resolution,[],[f324,f80])).
% 1.66/0.62  fof(f80,plain,(
% 1.66/0.62    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f25])).
% 1.66/0.62  fof(f25,plain,(
% 1.66/0.62    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.66/0.62    inference(ennf_transformation,[],[f18])).
% 1.66/0.62  fof(f18,axiom,(
% 1.66/0.62    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.66/0.62  fof(f324,plain,(
% 1.66/0.62    ( ! [X2] : (~m1_pre_topc(X2,sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X2)))) ) | ~spl6_41),
% 1.66/0.62    inference(avatar_component_clause,[],[f323])).
% 1.66/0.62  fof(f348,plain,(
% 1.66/0.62    spl6_43 | ~spl6_6 | ~spl6_13 | ~spl6_41),
% 1.66/0.62    inference(avatar_split_clause,[],[f344,f323,f185,f138,f346])).
% 1.66/0.62  fof(f344,plain,(
% 1.66/0.62    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (~spl6_6 | ~spl6_13 | ~spl6_41)),
% 1.66/0.62    inference(forward_demodulation,[],[f337,f186])).
% 1.66/0.62  fof(f337,plain,(
% 1.66/0.62    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (~spl6_6 | ~spl6_41)),
% 1.66/0.62    inference(resolution,[],[f324,f139])).
% 1.66/0.62  fof(f330,plain,(
% 1.66/0.62    ~spl6_8 | ~spl6_6 | spl6_40),
% 1.66/0.62    inference(avatar_split_clause,[],[f327,f319,f138,f146])).
% 1.66/0.62  fof(f327,plain,(
% 1.66/0.62    ~l1_pre_topc(sK0) | (~spl6_6 | spl6_40)),
% 1.66/0.62    inference(resolution,[],[f326,f139])).
% 1.66/0.62  fof(f326,plain,(
% 1.66/0.62    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | spl6_40),
% 1.66/0.62    inference(resolution,[],[f320,f81])).
% 1.66/0.62  fof(f320,plain,(
% 1.66/0.62    ~l1_pre_topc(sK1) | spl6_40),
% 1.66/0.62    inference(avatar_component_clause,[],[f319])).
% 1.66/0.62  fof(f325,plain,(
% 1.66/0.62    spl6_41 | ~spl6_9 | ~spl6_8 | spl6_10),
% 1.66/0.62    inference(avatar_split_clause,[],[f301,f154,f146,f150,f323])).
% 1.66/0.62  fof(f301,plain,(
% 1.66/0.62    ( ! [X2] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X2))) | ~m1_pre_topc(X2,sK0)) ) | spl6_10),
% 1.66/0.62    inference(resolution,[],[f290,f155])).
% 1.66/0.62  fof(f290,plain,(
% 1.66/0.62    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0)) )),
% 1.66/0.62    inference(duplicate_literal_removal,[],[f289])).
% 1.66/0.62  fof(f289,plain,(
% 1.66/0.62    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.66/0.62    inference(resolution,[],[f93,f82])).
% 1.66/0.62  fof(f279,plain,(
% 1.66/0.62    ~spl6_8 | spl6_31),
% 1.66/0.62    inference(avatar_split_clause,[],[f278,f275,f146])).
% 1.66/0.62  fof(f275,plain,(
% 1.66/0.62    spl6_31 <=> m1_pre_topc(sK0,sK0)),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.66/0.62  fof(f278,plain,(
% 1.66/0.62    ~l1_pre_topc(sK0) | spl6_31),
% 1.66/0.62    inference(resolution,[],[f276,f80])).
% 1.66/0.62  fof(f276,plain,(
% 1.66/0.62    ~m1_pre_topc(sK0,sK0) | spl6_31),
% 1.66/0.62    inference(avatar_component_clause,[],[f275])).
% 1.66/0.62  fof(f277,plain,(
% 1.66/0.62    ~spl6_8 | ~spl6_31 | spl6_27),
% 1.66/0.62    inference(avatar_split_clause,[],[f273,f259,f275,f146])).
% 1.66/0.62  fof(f273,plain,(
% 1.66/0.62    ~m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | spl6_27),
% 1.66/0.62    inference(resolution,[],[f260,f82])).
% 1.66/0.62  fof(f260,plain,(
% 1.66/0.62    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_27),
% 1.66/0.62    inference(avatar_component_clause,[],[f259])).
% 1.66/0.62  fof(f245,plain,(
% 1.66/0.62    ~spl6_8 | ~spl6_6 | spl6_21),
% 1.66/0.62    inference(avatar_split_clause,[],[f243,f227,f138,f146])).
% 1.66/0.62  fof(f243,plain,(
% 1.66/0.62    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl6_21),
% 1.66/0.62    inference(resolution,[],[f228,f82])).
% 1.66/0.62  fof(f228,plain,(
% 1.66/0.62    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_21),
% 1.66/0.62    inference(avatar_component_clause,[],[f227])).
% 1.66/0.62  fof(f191,plain,(
% 1.66/0.62    ~spl6_8 | spl6_14 | ~spl6_11),
% 1.66/0.62    inference(avatar_split_clause,[],[f179,f172,f189,f146])).
% 1.66/0.62  fof(f172,plain,(
% 1.66/0.62    spl6_11 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)))),
% 1.66/0.62    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.66/0.62  fof(f179,plain,(
% 1.66/0.62    k8_tmap_1(sK0,sK0) = k6_tmap_1(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~spl6_11),
% 1.66/0.62    inference(resolution,[],[f173,f80])).
% 1.66/0.62  fof(f173,plain,(
% 1.66/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0))) ) | ~spl6_11),
% 1.66/0.62    inference(avatar_component_clause,[],[f172])).
% 1.66/0.62  fof(f187,plain,(
% 1.66/0.62    spl6_13 | ~spl6_6 | ~spl6_11),
% 1.66/0.62    inference(avatar_split_clause,[],[f178,f172,f138,f185])).
% 1.66/0.62  fof(f178,plain,(
% 1.66/0.62    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_6 | ~spl6_11)),
% 1.66/0.62    inference(resolution,[],[f173,f139])).
% 1.66/0.62  fof(f174,plain,(
% 1.66/0.62    spl6_10 | ~spl6_8 | spl6_11 | ~spl6_9),
% 1.66/0.62    inference(avatar_split_clause,[],[f166,f150,f172,f146,f154])).
% 1.66/0.62  fof(f166,plain,(
% 1.66/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | k8_tmap_1(sK0,X0) = k6_tmap_1(sK0,u1_struct_0(X0)) | v2_struct_0(sK0)) ) | ~spl6_9),
% 1.66/0.62    inference(resolution,[],[f162,f151])).
% 1.66/0.62  fof(f151,plain,(
% 1.66/0.62    v2_pre_topc(sK0) | ~spl6_9),
% 1.66/0.62    inference(avatar_component_clause,[],[f150])).
% 1.66/0.62  fof(f162,plain,(
% 1.66/0.62    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f161,f99])).
% 1.66/0.62  fof(f99,plain,(
% 1.66/0.62    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f44])).
% 1.66/0.62  fof(f44,plain,(
% 1.66/0.62    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f43])).
% 1.66/0.62  fof(f43,plain,(
% 1.66/0.62    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f12])).
% 1.66/0.62  fof(f12,axiom,(
% 1.66/0.62    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 1.66/0.62  fof(f161,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f160,f100])).
% 1.66/0.62  fof(f100,plain,(
% 1.66/0.62    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f44])).
% 1.66/0.62  fof(f160,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(subsumption_resolution,[],[f157,f101])).
% 1.66/0.62  fof(f101,plain,(
% 1.66/0.62    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f44])).
% 1.66/0.62  fof(f157,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(global_subsumption,[],[f82,f113])).
% 1.66/0.62  fof(f113,plain,(
% 1.66/0.62    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(equality_resolution,[],[f112])).
% 1.66/0.62  fof(f112,plain,(
% 1.66/0.62    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(equality_resolution,[],[f84])).
% 1.66/0.62  fof(f84,plain,(
% 1.66/0.62    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.66/0.62    inference(cnf_transformation,[],[f62])).
% 1.66/0.62  fof(f62,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK4(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).
% 1.66/0.62  fof(f61,plain,(
% 1.66/0.62    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK4(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f60,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(rectify,[],[f59])).
% 1.66/0.62  fof(f59,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(nnf_transformation,[],[f31])).
% 1.66/0.62  fof(f31,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f30])).
% 1.66/0.62  fof(f30,plain,(
% 1.66/0.62    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f7])).
% 1.66/0.62  fof(f7,axiom,(
% 1.66/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).
% 1.66/0.62  fof(f156,plain,(
% 1.66/0.62    ~spl6_10),
% 1.66/0.62    inference(avatar_split_clause,[],[f67,f154])).
% 1.66/0.62  fof(f67,plain,(
% 1.66/0.62    ~v2_struct_0(sK0)),
% 1.66/0.62    inference(cnf_transformation,[],[f57])).
% 1.66/0.62  fof(f57,plain,(
% 1.66/0.62    (((~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.66/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f56,f55,f54,f53])).
% 1.66/0.62  fof(f53,plain,(
% 1.66/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f54,plain,(
% 1.66/0.62    ? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f55,plain,(
% 1.66/0.62    ? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) & r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f56,plain,(
% 1.66/0.62    ? [X3] : (~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.66/0.62    introduced(choice_axiom,[])).
% 1.66/0.62  fof(f22,plain,(
% 1.66/0.62    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.66/0.62    inference(flattening,[],[f21])).
% 1.66/0.62  fof(f21,plain,(
% 1.66/0.62    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.66/0.62    inference(ennf_transformation,[],[f20])).
% 1.66/0.62  fof(f20,negated_conjecture,(
% 1.66/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 1.66/0.62    inference(negated_conjecture,[],[f19])).
% 1.66/0.62  fof(f19,conjecture,(
% 1.66/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 1.66/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_tmap_1)).
% 1.66/0.62  fof(f152,plain,(
% 1.66/0.62    spl6_9),
% 1.66/0.62    inference(avatar_split_clause,[],[f68,f150])).
% 1.66/0.62  fof(f68,plain,(
% 1.66/0.62    v2_pre_topc(sK0)),
% 1.66/0.62    inference(cnf_transformation,[],[f57])).
% 1.66/0.62  fof(f148,plain,(
% 1.66/0.62    spl6_8),
% 1.66/0.62    inference(avatar_split_clause,[],[f69,f146])).
% 1.66/0.62  fof(f69,plain,(
% 1.66/0.62    l1_pre_topc(sK0)),
% 1.66/0.62    inference(cnf_transformation,[],[f57])).
% 1.66/0.62  fof(f140,plain,(
% 1.66/0.62    spl6_6),
% 1.66/0.62    inference(avatar_split_clause,[],[f71,f138])).
% 1.66/0.62  fof(f71,plain,(
% 1.66/0.62    m1_pre_topc(sK1,sK0)),
% 1.66/0.62    inference(cnf_transformation,[],[f57])).
% 1.66/0.62  fof(f136,plain,(
% 1.66/0.62    ~spl6_5),
% 1.66/0.62    inference(avatar_split_clause,[],[f72,f134])).
% 1.66/0.62  fof(f72,plain,(
% 1.66/0.62    ~v2_struct_0(sK2)),
% 1.66/0.62    inference(cnf_transformation,[],[f57])).
% 1.66/0.62  fof(f132,plain,(
% 1.66/0.62    spl6_4),
% 1.66/0.62    inference(avatar_split_clause,[],[f73,f130])).
% 1.66/0.62  fof(f73,plain,(
% 1.66/0.62    m1_pre_topc(sK2,sK0)),
% 1.66/0.62    inference(cnf_transformation,[],[f57])).
% 1.66/0.62  fof(f128,plain,(
% 1.66/0.62    spl6_3),
% 1.66/0.62    inference(avatar_split_clause,[],[f74,f126])).
% 1.66/0.62  fof(f74,plain,(
% 1.66/0.62    r1_tsep_1(sK1,sK2)),
% 1.66/0.62    inference(cnf_transformation,[],[f57])).
% 1.66/0.62  fof(f124,plain,(
% 1.66/0.62    spl6_2),
% 1.66/0.62    inference(avatar_split_clause,[],[f75,f122])).
% 1.66/0.62  fof(f75,plain,(
% 1.66/0.62    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.66/0.62    inference(cnf_transformation,[],[f57])).
% 1.66/0.62  fof(f120,plain,(
% 1.66/0.62    ~spl6_1),
% 1.66/0.62    inference(avatar_split_clause,[],[f76,f118])).
% 1.66/0.62  fof(f76,plain,(
% 1.66/0.62    ~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)),
% 1.66/0.62    inference(cnf_transformation,[],[f57])).
% 1.66/0.62  % SZS output end Proof for theBenchmark
% 1.66/0.62  % (22079)------------------------------
% 1.66/0.62  % (22079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (22079)Termination reason: Refutation
% 1.66/0.62  
% 1.66/0.62  % (22079)Memory used [KB]: 12792
% 1.66/0.62  % (22079)Time elapsed: 0.195 s
% 1.66/0.62  % (22079)------------------------------
% 1.66/0.62  % (22079)------------------------------
% 1.66/0.63  % (22072)Success in time 0.263 s
%------------------------------------------------------------------------------
