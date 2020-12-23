%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t116_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:04 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  354 (1024 expanded)
%              Number of leaves         :   67 ( 384 expanded)
%              Depth                    :   18
%              Number of atoms          : 1361 (3575 expanded)
%              Number of equality atoms :  135 ( 443 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1896,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f152,f159,f166,f173,f180,f187,f200,f203,f214,f237,f251,f288,f357,f382,f435,f438,f444,f457,f462,f477,f485,f489,f496,f504,f508,f566,f575,f595,f614,f621,f623,f770,f822,f857,f881,f895,f920,f928,f932,f934,f941,f1026,f1079,f1249,f1313,f1346,f1466,f1483,f1523,f1536,f1551,f1557,f1561,f1570,f1576,f1635,f1847,f1895])).

fof(f1895,plain,
    ( spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14
    | spl10_23
    | ~ spl10_56
    | ~ spl10_58 ),
    inference(avatar_contradiction_clause,[],[f1894])).

fof(f1894,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_23
    | ~ spl10_56
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f1893,f287])).

fof(f287,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl10_23
  <=> ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f1893,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_56
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f1892,f1309])).

fof(f1309,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f1308])).

fof(f1308,plain,
    ( spl10_58
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f1892,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_56 ),
    inference(trivial_inequality_removal,[],[f1891])).

fof(f1891,plain,
    ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_56 ),
    inference(superposition,[],[f1876,f1248])).

fof(f1248,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f1247])).

fof(f1247,plain,
    ( spl10_56
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f1876,plain,
    ( ! [X2] :
        ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X2,sK0) )
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f1875,f158])).

fof(f158,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl10_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f1875,plain,
    ( ! [X2] :
        ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | v3_pre_topc(X2,sK0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f1874,f172])).

fof(f172,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl10_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f1874,plain,
    ( ! [X2] :
        ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X2)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | v3_pre_topc(X2,sK0) )
    | ~ spl10_4
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f1852,f165])).

fof(f165,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl10_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f1852,plain,
    ( ! [X2] :
        ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,X2)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | v3_pre_topc(X2,sK0) )
    | ~ spl10_14 ),
    inference(superposition,[],[f113,f199])).

fof(f199,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl10_14
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f113,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',t106_tmap_1)).

fof(f1847,plain,
    ( spl10_14
    | ~ spl10_42
    | ~ spl10_46
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f1041,f939,f768,f564,f198])).

fof(f564,plain,
    ( spl10_42
  <=> g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) = k8_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f768,plain,
    ( spl10_46
  <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f939,plain,
    ( spl10_54
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f1041,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl10_42
    | ~ spl10_46
    | ~ spl10_54 ),
    inference(backward_demodulation,[],[f940,f952])).

fof(f952,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl10_42
    | ~ spl10_46 ),
    inference(forward_demodulation,[],[f565,f769])).

fof(f769,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f768])).

fof(f565,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) = k8_tmap_1(sK0,sK1)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f564])).

fof(f940,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f939])).

fof(f1635,plain,
    ( ~ spl10_79
    | spl10_80
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f1577,f1515,f1633,f1627])).

fof(f1627,plain,
    ( spl10_79
  <=> ~ l1_pre_topc(sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f1633,plain,
    ( spl10_80
  <=> v1_pre_topc(sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f1515,plain,
    ( spl10_64
  <=> g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f1577,plain,
    ( v1_pre_topc(sK7(sK1))
    | ~ l1_pre_topc(sK7(sK1))
    | ~ spl10_64 ),
    inference(superposition,[],[f216,f1516])).

fof(f1516,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1)
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f1515])).

fof(f216,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f121,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',dt_g1_pre_topc)).

fof(f121,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',dt_u1_pre_topc)).

fof(f1576,plain,
    ( spl10_64
    | spl10_73
    | spl10_75 ),
    inference(avatar_split_clause,[],[f1559,f1549,f1543,f1515])).

fof(f1543,plain,
    ( spl10_73
  <=> ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))),sK7(sK1)),g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_73])])).

fof(f1549,plain,
    ( spl10_75
  <=> ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))),sK7(sK1)),sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f1559,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1)
    | ~ spl10_73
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f1558,f1550])).

fof(f1550,plain,
    ( ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))),sK7(sK1)),sK7(sK1))
    | ~ spl10_75 ),
    inference(avatar_component_clause,[],[f1549])).

fof(f1558,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))),sK7(sK1)),sK7(sK1))
    | g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1)
    | ~ spl10_73 ),
    inference(resolution,[],[f1544,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',t2_tarski)).

fof(f1544,plain,
    ( ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))),sK7(sK1)),g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))))
    | ~ spl10_73 ),
    inference(avatar_component_clause,[],[f1543])).

fof(f1570,plain,
    ( ~ spl10_77
    | spl10_73
    | spl10_75 ),
    inference(avatar_split_clause,[],[f1562,f1549,f1543,f1568])).

fof(f1568,plain,
    ( spl10_77
  <=> ~ r2_hidden(sK2(sK7(sK1),sK7(sK1)),sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f1562,plain,
    ( ~ r2_hidden(sK2(sK7(sK1),sK7(sK1)),sK7(sK1))
    | ~ spl10_73
    | ~ spl10_75 ),
    inference(backward_demodulation,[],[f1559,f1544])).

fof(f1561,plain,
    ( spl10_65
    | spl10_73
    | spl10_75 ),
    inference(avatar_contradiction_clause,[],[f1560])).

fof(f1560,plain,
    ( $false
    | ~ spl10_65
    | ~ spl10_73
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f1559,f1513])).

fof(f1513,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) != sK7(sK1)
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f1512])).

fof(f1512,plain,
    ( spl10_65
  <=> g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) != sK7(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f1557,plain,
    ( spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | spl10_69 ),
    inference(avatar_contradiction_clause,[],[f1556])).

fof(f1556,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f1555,f165])).

fof(f1555,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f1554,f158])).

fof(f1554,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_6
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f1553,f172])).

fof(f1553,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl10_69 ),
    inference(resolution,[],[f1529,f219])).

fof(f219,plain,(
    ! [X0] :
      ( l1_pre_topc(sK7(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(sK7(X0)) ) ),
    inference(resolution,[],[f130,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',dt_m1_pre_topc)).

fof(f130,plain,(
    ! [X0] :
      ( m1_pre_topc(sK7(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tsep_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tsep_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_tsep_1(X1,X0)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',rc2_tsep_1)).

fof(f1529,plain,
    ( ~ l1_pre_topc(sK7(sK0))
    | ~ spl10_69 ),
    inference(avatar_component_clause,[],[f1528])).

fof(f1528,plain,
    ( spl10_69
  <=> ~ l1_pre_topc(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f1551,plain,
    ( ~ spl10_73
    | ~ spl10_75
    | spl10_65 ),
    inference(avatar_split_clause,[],[f1537,f1512,f1549,f1543])).

fof(f1537,plain,
    ( ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))),sK7(sK1)),sK7(sK1))
    | ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))),sK7(sK1)),g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))))
    | ~ spl10_65 ),
    inference(extensionality_resolution,[],[f100,f1513])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1536,plain,
    ( ~ spl10_69
    | spl10_70
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f1484,f1481,f1534,f1528])).

fof(f1534,plain,
    ( spl10_70
  <=> v1_pre_topc(sK7(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f1481,plain,
    ( spl10_62
  <=> g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f1484,plain,
    ( v1_pre_topc(sK7(sK0))
    | ~ l1_pre_topc(sK7(sK0))
    | ~ spl10_62 ),
    inference(superposition,[],[f216,f1482])).

fof(f1482,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0)
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f1481])).

fof(f1523,plain,
    ( spl10_64
    | ~ spl10_67
    | spl10_1
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f791,f212,f150,f1521,f1515])).

fof(f1521,plain,
    ( spl10_67
  <=> ~ v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f150,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f212,plain,
    ( spl10_16
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f791,plain,
    ( ~ v2_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1)
    | ~ spl10_1
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f783,f151])).

fof(f151,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f150])).

fof(f783,plain,
    ( ~ v2_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK7(sK1)),u1_pre_topc(sK7(sK1))) = sK7(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_16 ),
    inference(resolution,[],[f221,f213])).

fof(f213,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f212])).

fof(f221,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(sK7(X0)),u1_pre_topc(sK7(X0))) = sK7(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f220,f219])).

fof(f220,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK7(X0))
      | g1_pre_topc(u1_struct_0(sK7(X0)),u1_pre_topc(sK7(X0))) = sK7(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f103,f132])).

fof(f132,plain,(
    ! [X0] :
      ( v1_pre_topc(sK7(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',abstractness_v1_pre_topc)).

fof(f1483,plain,
    ( spl10_62
    | spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f790,f171,f164,f157,f1481])).

fof(f790,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f789,f158])).

fof(f789,plain,
    ( g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f782,f165])).

fof(f782,plain,
    ( ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK7(sK0)),u1_pre_topc(sK7(sK0))) = sK7(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_6 ),
    inference(resolution,[],[f221,f172])).

fof(f1466,plain,
    ( spl10_60
    | spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_56
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f1404,f1308,f1247,f171,f164,f157,f1464])).

fof(f1464,plain,
    ( spl10_60
  <=> v2_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f1404,plain,
    ( v2_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_56
    | ~ spl10_58 ),
    inference(forward_demodulation,[],[f1403,f1248])).

fof(f1403,plain,
    ( v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f1402,f158])).

fof(f1402,plain,
    ( v2_struct_0(sK0)
    | v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f1401,f172])).

fof(f1401,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl10_4
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f1380,f165])).

fof(f1380,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl10_58 ),
    inference(resolution,[],[f1309,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',dt_k6_tmap_1)).

fof(f1346,plain,
    ( ~ spl10_6
    | ~ spl10_8
    | spl10_59 ),
    inference(avatar_contradiction_clause,[],[f1345])).

fof(f1345,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f1344,f172])).

fof(f1344,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_8
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f1343,f179])).

fof(f179,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl10_8
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f1343,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_59 ),
    inference(resolution,[],[f1312,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',t1_tsep_1)).

fof(f1312,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_59 ),
    inference(avatar_component_clause,[],[f1311])).

fof(f1311,plain,
    ( spl10_59
  <=> ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f1313,plain,
    ( ~ spl10_59
    | spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | spl10_23
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_46
    | ~ spl10_54
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f1293,f1247,f939,f768,f564,f499,f286,f171,f164,f157,f1311])).

fof(f499,plain,
    ( spl10_40
  <=> r2_hidden(sK2(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f1293,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_23
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_46
    | ~ spl10_54
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f1292,f500])).

fof(f500,plain,
    ( r2_hidden(sK2(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f499])).

fof(f1292,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_23
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_46
    | ~ spl10_54
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f1291,f1041])).

fof(f1291,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k8_tmap_1(sK0,sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_23
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_46
    | ~ spl10_54
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f1290,f1248])).

fof(f1290,plain,
    ( ~ r2_hidden(sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_23
    | ~ spl10_40
    | ~ spl10_42
    | ~ spl10_46
    | ~ spl10_54
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f1289,f500])).

fof(f1289,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1))
    | ~ r2_hidden(sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_23
    | ~ spl10_42
    | ~ spl10_46
    | ~ spl10_54
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f1288,f1041])).

fof(f1288,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_23
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f1287,f287])).

fof(f1287,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f1286,f158])).

fof(f1286,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f1285,f172])).

fof(f1285,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f1283,f165])).

fof(f1283,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(sK2(k6_tmap_1(sK0,u1_struct_0(sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_56 ),
    inference(superposition,[],[f295,f1248])).

fof(f295,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK2(k6_tmap_1(X2,X3),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ r2_hidden(sK2(k6_tmap_1(X2,X3),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),k6_tmap_1(X2,X3))
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v2_struct_0(X2)
      | v3_pre_topc(X3,X2) ) ),
    inference(extensionality_resolution,[],[f100,f113])).

fof(f1249,plain,
    ( spl10_56
    | spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f830,f178,f171,f164,f157,f1247])).

fof(f830,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f829,f158])).

fof(f829,plain,
    ( v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f828,f165])).

fof(f828,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f823,f172])).

fof(f823,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl10_8 ),
    inference(resolution,[],[f309,f179])).

fof(f309,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f145,f129])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f144,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',dt_k8_tmap_1)).

fof(f144,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f143,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f143,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f139,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f139,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X3
      | k6_tmap_1(X0,X3) = X2
      | k8_tmap_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
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
    inference(flattening,[],[f69])).

fof(f69,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',d11_tmap_1)).

fof(f1079,plain,
    ( ~ spl10_13
    | ~ spl10_6
    | ~ spl10_8
    | spl10_23 ),
    inference(avatar_split_clause,[],[f612,f286,f178,f171,f189])).

fof(f189,plain,
    ( spl10_13
  <=> ~ v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f612,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f611,f179])).

fof(f611,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl10_6
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f610,f172])).

fof(f610,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl10_23 ),
    inference(resolution,[],[f293,f287])).

fof(f293,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X0),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ v1_tsep_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | v3_pre_topc(u1_struct_0(X0),X1)
      | ~ v1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f141,f129])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',d1_tsep_1)).

fof(f1026,plain,
    ( spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | spl10_15
    | ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f1025])).

fof(f1025,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_15
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f1024,f196])).

fof(f196,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl10_15
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f1024,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_22 ),
    inference(forward_demodulation,[],[f1023,f830])).

fof(f1023,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f1022,f179])).

fof(f1022,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f1021,f165])).

fof(f1021,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f1020,f158])).

fof(f1020,plain,
    ( v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_6
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f1018,f172])).

fof(f1018,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl10_22 ),
    inference(resolution,[],[f303,f284])).

fof(f284,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl10_22
  <=> v3_pre_topc(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f303,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f114,f129])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f941,plain,
    ( spl10_54
    | ~ spl10_26
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f712,f564,f355,f939])).

fof(f355,plain,
    ( spl10_26
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != k8_tmap_1(sK0,sK1)
        | u1_struct_0(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f712,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl10_26
    | ~ spl10_42 ),
    inference(trivial_inequality_removal,[],[f705])).

fof(f705,plain,
    ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl10_26
    | ~ spl10_42 ),
    inference(superposition,[],[f356,f565])).

fof(f356,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != k8_tmap_1(sK0,sK1)
        | u1_struct_0(sK0) = X0 )
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f355])).

fof(f934,plain,
    ( spl10_46
    | spl10_49
    | spl10_51 ),
    inference(avatar_split_clause,[],[f879,f855,f849,f768])).

fof(f849,plain,
    ( spl10_49
  <=> ~ r2_hidden(sK2(u1_pre_topc(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f855,plain,
    ( spl10_51
  <=> ~ r2_hidden(sK2(u1_pre_topc(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f879,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_49
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f878,f850])).

fof(f850,plain,
    ( ~ r2_hidden(sK2(u1_pre_topc(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))),u1_pre_topc(sK0))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f849])).

fof(f878,plain,
    ( r2_hidden(sK2(u1_pre_topc(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_51 ),
    inference(resolution,[],[f856,f99])).

fof(f856,plain,
    ( ~ r2_hidden(sK2(u1_pre_topc(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f855])).

fof(f932,plain,
    ( spl10_40
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_42
    | spl10_49
    | spl10_51 ),
    inference(avatar_split_clause,[],[f903,f855,f849,f564,f446,f355,f499])).

fof(f446,plain,
    ( spl10_30
  <=> r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k8_tmap_1(sK0,sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f903,plain,
    ( r2_hidden(sK2(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1))
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_42
    | ~ spl10_49
    | ~ spl10_51 ),
    inference(backward_demodulation,[],[f887,f447])).

fof(f447,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k8_tmap_1(sK0,sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f446])).

fof(f887,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl10_26
    | ~ spl10_42
    | ~ spl10_49
    | ~ spl10_51 ),
    inference(backward_demodulation,[],[f879,f858])).

fof(f858,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) = k8_tmap_1(sK0,sK1)
    | ~ spl10_26
    | ~ spl10_42 ),
    inference(backward_demodulation,[],[f712,f565])).

fof(f928,plain,
    ( ~ spl10_53
    | spl10_49
    | spl10_51 ),
    inference(avatar_split_clause,[],[f885,f855,f849,f926])).

fof(f926,plain,
    ( spl10_53
  <=> ~ r2_hidden(sK2(u1_pre_topc(sK0),u1_pre_topc(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f885,plain,
    ( ~ r2_hidden(sK2(u1_pre_topc(sK0),u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ spl10_49
    | ~ spl10_51 ),
    inference(backward_demodulation,[],[f879,f850])).

fof(f920,plain,
    ( ~ spl10_13
    | ~ spl10_6
    | ~ spl10_8
    | spl10_23 ),
    inference(avatar_split_clause,[],[f612,f286,f178,f171,f189])).

fof(f895,plain,
    ( spl10_15
    | ~ spl10_26
    | ~ spl10_42
    | spl10_49
    | spl10_51 ),
    inference(avatar_contradiction_clause,[],[f894])).

fof(f894,plain,
    ( $false
    | ~ spl10_15
    | ~ spl10_26
    | ~ spl10_42
    | ~ spl10_49
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f887,f196])).

fof(f881,plain,
    ( spl10_47
    | spl10_49
    | spl10_51 ),
    inference(avatar_contradiction_clause,[],[f880])).

fof(f880,plain,
    ( $false
    | ~ spl10_47
    | ~ spl10_49
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f879,f766])).

fof(f766,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f765])).

fof(f765,plain,
    ( spl10_47
  <=> u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f857,plain,
    ( ~ spl10_49
    | ~ spl10_51
    | spl10_47 ),
    inference(avatar_split_clause,[],[f843,f765,f855,f849])).

fof(f843,plain,
    ( ~ r2_hidden(sK2(u1_pre_topc(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ r2_hidden(sK2(u1_pre_topc(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))),u1_pre_topc(sK0))
    | ~ spl10_47 ),
    inference(extensionality_resolution,[],[f100,f766])).

fof(f822,plain,
    ( spl10_12
    | ~ spl10_23
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f266,f249,f178,f171,f286,f192])).

fof(f192,plain,
    ( spl10_12
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f249,plain,
    ( spl10_20
  <=> u1_struct_0(sK1) = sK6(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f266,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f265,f172])).

fof(f265,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl10_8
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f264,f179])).

fof(f264,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl10_20 ),
    inference(superposition,[],[f128,f250])).

fof(f250,plain,
    ( u1_struct_0(sK1) = sK6(sK0,sK1)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f249])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK6(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f770,plain,
    ( spl10_46
    | ~ spl10_14
    | ~ spl10_24
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f711,f564,f349,f198,f768])).

fof(f349,plain,
    ( spl10_24
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f711,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_14
    | ~ spl10_24
    | ~ spl10_42 ),
    inference(trivial_inequality_removal,[],[f706])).

fof(f706,plain,
    ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_14
    | ~ spl10_24
    | ~ spl10_42 ),
    inference(superposition,[],[f652,f565])).

fof(f652,plain,
    ( ! [X8,X7] :
        ( g1_pre_topc(X7,X8) != k8_tmap_1(sK0,sK1)
        | u1_pre_topc(sK0) = X8 )
    | ~ spl10_14
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f631,f350])).

fof(f350,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f349])).

fof(f631,plain,
    ( ! [X8,X7] :
        ( g1_pre_topc(X7,X8) != k8_tmap_1(sK0,sK1)
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | u1_pre_topc(sK0) = X8 )
    | ~ spl10_14 ),
    inference(superposition,[],[f102,f199])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',free_g1_pre_topc)).

fof(f623,plain,
    ( spl10_14
    | spl10_35
    | spl10_37 ),
    inference(avatar_split_clause,[],[f487,f475,f469,f198])).

fof(f469,plain,
    ( spl10_35
  <=> ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f475,plain,
    ( spl10_37
  <=> ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f487,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl10_35
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f486,f470])).

fof(f470,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k8_tmap_1(sK0,sK1))
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f469])).

fof(f486,plain,
    ( r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k8_tmap_1(sK0,sK1))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl10_37 ),
    inference(resolution,[],[f476,f99])).

fof(f476,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f475])).

fof(f621,plain,
    ( ~ spl10_13
    | ~ spl10_6
    | ~ spl10_8
    | spl10_23 ),
    inference(avatar_split_clause,[],[f612,f286,f178,f171,f189])).

fof(f614,plain,
    ( ~ spl10_6
    | ~ spl10_8
    | ~ spl10_12
    | spl10_23 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f612,f193])).

fof(f193,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f192])).

fof(f595,plain,
    ( spl10_44
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f405,f349,f593])).

fof(f593,plain,
    ( spl10_44
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f405,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_24 ),
    inference(resolution,[],[f350,f111])).

fof(f575,plain,
    ( spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | spl10_19 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f573,f158])).

fof(f573,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f572,f179])).

fof(f572,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f571,f172])).

fof(f571,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f570,f165])).

fof(f570,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_19 ),
    inference(resolution,[],[f233,f106])).

fof(f233,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl10_19
  <=> ~ l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f566,plain,
    ( spl10_42
    | ~ spl10_18
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f464,f433,f235,f564])).

fof(f235,plain,
    ( spl10_18
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f433,plain,
    ( spl10_28
  <=> v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f464,plain,
    ( g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) = k8_tmap_1(sK0,sK1)
    | ~ spl10_18
    | ~ spl10_28 ),
    inference(subsumption_resolution,[],[f463,f236])).

fof(f236,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f235])).

fof(f463,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) = k8_tmap_1(sK0,sK1)
    | ~ spl10_28 ),
    inference(resolution,[],[f434,f103])).

fof(f434,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f433])).

fof(f508,plain,
    ( spl10_14
    | spl10_35
    | spl10_37 ),
    inference(avatar_split_clause,[],[f487,f475,f469,f198])).

fof(f504,plain,
    ( ~ spl10_41
    | spl10_33
    | spl10_35
    | spl10_37 ),
    inference(avatar_split_clause,[],[f491,f475,f469,f455,f502])).

fof(f502,plain,
    ( spl10_41
  <=> ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f455,plain,
    ( spl10_33
  <=> ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f491,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1))
    | ~ spl10_33
    | ~ spl10_35
    | ~ spl10_37 ),
    inference(backward_demodulation,[],[f487,f456])).

fof(f456,plain,
    ( ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1))
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f455])).

fof(f496,plain,
    ( ~ spl10_13
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f202,f198,f189])).

fof(f202,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ spl10_14 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( k8_tmap_1(sK0,sK1) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl10_14 ),
    inference(backward_demodulation,[],[f199,f142])).

fof(f142,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f86,f90])).

fof(f90,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',t116_tmap_1)).

fof(f86,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f489,plain,
    ( spl10_15
    | spl10_35
    | spl10_37 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | ~ spl10_15
    | ~ spl10_35
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f487,f196])).

fof(f485,plain,
    ( spl10_38
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f404,f349,f483])).

fof(f483,plain,
    ( spl10_38
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f404,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_24 ),
    inference(resolution,[],[f350,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f477,plain,
    ( ~ spl10_35
    | ~ spl10_37
    | spl10_15 ),
    inference(avatar_split_clause,[],[f437,f195,f475,f469])).

fof(f437,plain,
    ( ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ r2_hidden(sK2(k8_tmap_1(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k8_tmap_1(sK0,sK1))
    | ~ spl10_15 ),
    inference(extensionality_resolution,[],[f100,f196])).

fof(f462,plain,
    ( spl10_15
    | spl10_31
    | spl10_33 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl10_15
    | ~ spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f460,f196])).

fof(f460,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl10_31
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f459,f456])).

fof(f459,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl10_31 ),
    inference(resolution,[],[f450,f99])).

fof(f450,plain,
    ( ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k8_tmap_1(sK0,sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl10_31
  <=> ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k8_tmap_1(sK0,sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f457,plain,
    ( ~ spl10_31
    | ~ spl10_33
    | spl10_15 ),
    inference(avatar_split_clause,[],[f436,f195,f455,f449])).

fof(f436,plain,
    ( ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k8_tmap_1(sK0,sK1)),k8_tmap_1(sK0,sK1))
    | ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),k8_tmap_1(sK0,sK1)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_15 ),
    inference(extensionality_resolution,[],[f100,f196])).

fof(f444,plain,
    ( spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | spl10_29 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f442,f158])).

fof(f442,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f441,f179])).

fof(f441,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f440,f172])).

fof(f440,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f439,f165])).

fof(f439,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl10_29 ),
    inference(resolution,[],[f431,f104])).

fof(f431,plain,
    ( ~ v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl10_29
  <=> ~ v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f438,plain,
    ( ~ spl10_13
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f142,f195,f189])).

fof(f435,plain,
    ( spl10_28
    | ~ spl10_14
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f411,f349,f198,f433])).

fof(f411,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_14
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f405,f199])).

fof(f382,plain,
    ( ~ spl10_6
    | spl10_25 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f380,f172])).

fof(f380,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_25 ),
    inference(resolution,[],[f353,f121])).

fof(f353,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl10_25
  <=> ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f357,plain,
    ( ~ spl10_25
    | spl10_26
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f254,f198,f355,f352])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != k8_tmap_1(sK0,sK1)
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | u1_struct_0(sK0) = X0 )
    | ~ spl10_14 ),
    inference(superposition,[],[f101,f199])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f288,plain,
    ( ~ spl10_23
    | ~ spl10_6
    | ~ spl10_8
    | spl10_13
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f267,f249,f189,f178,f171,f286])).

fof(f267,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_13
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f266,f190])).

fof(f190,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f189])).

fof(f251,plain,
    ( spl10_20
    | ~ spl10_6
    | ~ spl10_8
    | spl10_13 ),
    inference(avatar_split_clause,[],[f244,f189,f178,f171,f249])).

fof(f244,plain,
    ( u1_struct_0(sK1) = sK6(sK0,sK1)
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f243,f172])).

fof(f243,plain,
    ( u1_struct_0(sK1) = sK6(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_8
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f242,f179])).

fof(f242,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | u1_struct_0(sK1) = sK6(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl10_13 ),
    inference(resolution,[],[f127,f190])).

fof(f127,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK6(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f237,plain,
    ( spl10_18
    | ~ spl10_6
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f224,f198,f171,f235])).

fof(f224,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl10_6
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f223,f172])).

fof(f223,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_14 ),
    inference(superposition,[],[f215,f199])).

fof(f215,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f121,f112])).

fof(f214,plain,
    ( spl10_16
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f207,f178,f171,f212])).

fof(f207,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f204,f172])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl10_8 ),
    inference(resolution,[],[f136,f179])).

fof(f203,plain,
    ( ~ spl10_13
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f202,f198,f189])).

fof(f200,plain,
    ( spl10_12
    | spl10_14 ),
    inference(avatar_split_clause,[],[f87,f198,f192])).

fof(f87,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f187,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f137,f185])).

fof(f185,plain,
    ( spl10_10
  <=> l1_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f137,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t116_tmap_1.p',existence_l1_pre_topc)).

fof(f180,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f90,f178])).

fof(f173,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f93,f171])).

fof(f93,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f166,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f92,f164])).

fof(f92,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f159,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f91,f157])).

fof(f91,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f152,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f89,f150])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
