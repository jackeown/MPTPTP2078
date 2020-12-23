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
% DateTime   : Thu Dec  3 13:19:35 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  295 ( 635 expanded)
%              Number of leaves         :   56 ( 275 expanded)
%              Depth                    :   17
%              Number of atoms          : 1450 (2954 expanded)
%              Number of equality atoms :  108 ( 145 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f992,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f112,f117,f127,f132,f137,f142,f147,f152,f160,f165,f183,f194,f208,f218,f311,f331,f360,f403,f533,f574,f587,f627,f633,f652,f692,f733,f775,f857,f907,f915,f952,f961,f977,f982,f991])).

fof(f991,plain,
    ( ~ spl6_11
    | spl6_86 ),
    inference(avatar_contradiction_clause,[],[f990])).

fof(f990,plain,
    ( $false
    | ~ spl6_11
    | spl6_86 ),
    inference(subsumption_resolution,[],[f988,f159])).

fof(f159,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_11
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f988,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_86 ),
    inference(resolution,[],[f976,f70])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f976,plain,
    ( ~ l1_struct_0(sK1)
    | spl6_86 ),
    inference(avatar_component_clause,[],[f974])).

fof(f974,plain,
    ( spl6_86
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f982,plain,
    ( ~ spl6_12
    | spl6_85 ),
    inference(avatar_contradiction_clause,[],[f981])).

fof(f981,plain,
    ( $false
    | ~ spl6_12
    | spl6_85 ),
    inference(subsumption_resolution,[],[f979,f164])).

fof(f164,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl6_12
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

% (3473)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f979,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_85 ),
    inference(resolution,[],[f972,f70])).

fof(f972,plain,
    ( ~ l1_struct_0(sK2)
    | spl6_85 ),
    inference(avatar_component_clause,[],[f970])).

fof(f970,plain,
    ( spl6_85
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f977,plain,
    ( ~ spl6_85
    | ~ spl6_86
    | ~ spl6_16
    | spl6_83 ),
    inference(avatar_split_clause,[],[f964,f958,f191,f974,f970])).

fof(f191,plain,
    ( spl6_16
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f958,plain,
    ( spl6_83
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f964,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ spl6_16
    | spl6_83 ),
    inference(subsumption_resolution,[],[f963,f193])).

fof(f193,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f191])).

fof(f963,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | spl6_83 ),
    inference(resolution,[],[f960,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f960,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_83 ),
    inference(avatar_component_clause,[],[f958])).

fof(f961,plain,
    ( ~ spl6_83
    | spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | spl6_15
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f956,f950,f180,f144,f134,f124,f958])).

fof(f124,plain,
    ( spl6_5
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f134,plain,
    ( spl6_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f144,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f180,plain,
    ( spl6_15
  <=> r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f950,plain,
    ( spl6_82
  <=> ! [X1,X0] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f956,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | spl6_15
    | ~ spl6_82 ),
    inference(subsumption_resolution,[],[f955,f126])).

fof(f126,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f955,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ spl6_7
    | ~ spl6_9
    | spl6_15
    | ~ spl6_82 ),
    inference(subsumption_resolution,[],[f954,f136])).

fof(f136,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f954,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ spl6_9
    | spl6_15
    | ~ spl6_82 ),
    inference(subsumption_resolution,[],[f953,f146])).

fof(f146,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f953,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | spl6_15
    | ~ spl6_82 ),
    inference(resolution,[],[f951,f182])).

fof(f182,plain,
    ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f180])).

fof(f951,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f950])).

fof(f952,plain,
    ( spl6_82
    | ~ spl6_63
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f916,f904,f731,f950])).

fof(f731,plain,
    ( spl6_63
  <=> ! [X1,X0] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f904,plain,
    ( spl6_80
  <=> k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f916,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl6_63
    | ~ spl6_80 ),
    inference(backward_demodulation,[],[f732,f906])).

fof(f906,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f904])).

fof(f732,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f731])).

fof(f915,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_79 ),
    inference(avatar_contradiction_clause,[],[f914])).

fof(f914,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_79 ),
    inference(subsumption_resolution,[],[f913,f106])).

fof(f106,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f913,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | spl6_79 ),
    inference(subsumption_resolution,[],[f912,f111])).

fof(f111,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f912,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_6
    | spl6_79 ),
    inference(subsumption_resolution,[],[f911,f116])).

fof(f116,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f911,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_79 ),
    inference(subsumption_resolution,[],[f909,f131])).

fof(f131,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f909,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl6_79 ),
    inference(resolution,[],[f902,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
        & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
        & v1_funct_1(k9_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(f902,plain,
    ( ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | spl6_79 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl6_79
  <=> v1_funct_1(k9_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f907,plain,
    ( ~ spl6_79
    | spl6_80
    | spl6_22
    | ~ spl6_36
    | ~ spl6_42
    | ~ spl6_44
    | ~ spl6_51
    | ~ spl6_52
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f898,f689,f649,f624,f584,f571,f530,f286,f904,f900])).

fof(f286,plain,
    ( spl6_22
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f530,plain,
    ( spl6_36
  <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f571,plain,
    ( spl6_42
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f584,plain,
    ( spl6_44
  <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f624,plain,
    ( spl6_51
  <=> v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f649,plain,
    ( spl6_52
  <=> v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f689,plain,
    ( spl6_56
  <=> m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f898,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | spl6_22
    | ~ spl6_36
    | ~ spl6_42
    | ~ spl6_44
    | ~ spl6_51
    | ~ spl6_52
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f847,f288])).

fof(f288,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f286])).

fof(f847,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_36
    | ~ spl6_42
    | ~ spl6_44
    | ~ spl6_51
    | ~ spl6_52
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f846,f586])).

fof(f586,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f584])).

fof(f846,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_36
    | ~ spl6_42
    | ~ spl6_51
    | ~ spl6_52
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f845,f651])).

% (3461)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f651,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f649])).

fof(f845,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_36
    | ~ spl6_42
    | ~ spl6_51
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f844,f626])).

fof(f626,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f624])).

fof(f844,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_36
    | ~ spl6_42
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f577,f691])).

fof(f691,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f689])).

fof(f577,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_36
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f576,f532])).

fof(f532,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f530])).

fof(f576,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_42 ),
    inference(duplicate_literal_removal,[],[f575])).

fof(f575,plain,
    ( k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k9_tmap_1(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_42 ),
    inference(resolution,[],[f573,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f573,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f571])).

fof(f857,plain,
    ( spl6_1
    | ~ spl6_22
    | ~ spl6_69 ),
    inference(avatar_contradiction_clause,[],[f856])).

fof(f856,plain,
    ( $false
    | spl6_1
    | ~ spl6_22
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f855,f106])).

fof(f855,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_22
    | ~ spl6_69 ),
    inference(subsumption_resolution,[],[f853,f760])).

fof(f760,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f759])).

fof(f759,plain,
    ( spl6_69
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f853,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_22 ),
    inference(resolution,[],[f287,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f287,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f286])).

fof(f775,plain,
    ( ~ spl6_3
    | spl6_69 ),
    inference(avatar_contradiction_clause,[],[f774])).

fof(f774,plain,
    ( $false
    | ~ spl6_3
    | spl6_69 ),
    inference(subsumption_resolution,[],[f772,f116])).

fof(f772,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_69 ),
    inference(resolution,[],[f761,f70])).

fof(f761,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_69 ),
    inference(avatar_component_clause,[],[f759])).

fof(f733,plain,
    ( spl6_63
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f725,f620,f328,f114,f109,f104,f731])).

fof(f328,plain,
    ( spl6_25
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f620,plain,
    ( spl6_50
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f725,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f506,f621])).

fof(f621,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f620])).

fof(f506,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f505,f106])).

fof(f505,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f504,f111])).

fof(f504,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f501,f116])).

fof(f501,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_25 ),
    inference(superposition,[],[f84,f330])).

fof(f330,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f328])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_xboole_0(u1_struct_0(X2),X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f692,plain,
    ( spl6_56
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_31
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f687,f620,f400,f328,f114,f109,f104,f689])).

fof(f400,plain,
    ( spl6_31
  <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f687,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_31
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f510,f621])).

fof(f510,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f509,f402])).

fof(f402,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f400])).

fof(f509,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f508,f106])).

fof(f508,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f507,f111])).

fof(f507,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f502,f116])).

fof(f502,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_25 ),
    inference(superposition,[],[f93,f330])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f652,plain,
    ( spl6_52
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f647,f620,f114,f109,f104,f649])).

fof(f647,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f646,f106])).

fof(f646,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f645,f111])).

fof(f645,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f636,f116])).

fof(f636,plain,
    ( v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_50 ),
    inference(resolution,[],[f621,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f633,plain,
    ( ~ spl6_3
    | ~ spl6_6
    | spl6_50 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_6
    | spl6_50 ),
    inference(subsumption_resolution,[],[f631,f116])).

fof(f631,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_6
    | spl6_50 ),
    inference(subsumption_resolution,[],[f629,f131])).

fof(f629,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_50 ),
    inference(resolution,[],[f622,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f622,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_50 ),
    inference(avatar_component_clause,[],[f620])).

fof(f627,plain,
    ( ~ spl6_50
    | spl6_51
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f514,f400,f328,f114,f109,f104,f624,f620])).

fof(f514,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f513,f402])).

fof(f513,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f512,f106])).

fof(f512,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f511,f111])).

fof(f511,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f503,f116])).

fof(f503,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_25 ),
    inference(superposition,[],[f92,f330])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f587,plain,
    ( spl6_44
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f430,f400,f129,f114,f109,f104,f584])).

fof(f430,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f429,f106])).

fof(f429,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f428,f111])).

fof(f428,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f427,f116])).

fof(f427,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f408,f131])).

fof(f408,plain,
    ( m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_31 ),
    inference(superposition,[],[f90,f402])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f574,plain,
    ( spl6_42
    | ~ spl6_6
    | ~ spl6_25
    | ~ spl6_28
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f564,f400,f358,f328,f129,f571])).

fof(f358,plain,
    ( spl6_28
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f564,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_6
    | ~ spl6_25
    | ~ spl6_28
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f563,f402])).

fof(f563,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_6
    | ~ spl6_25
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f362,f330])).

fof(f362,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_6
    | ~ spl6_28 ),
    inference(resolution,[],[f359,f131])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0))) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f358])).

fof(f533,plain,
    ( spl6_36
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f434,f400,f129,f114,f109,f104,f530])).

fof(f434,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f433,f106])).

fof(f433,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f432,f111])).

fof(f432,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f431,f116])).

fof(f431,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f409,f131])).

fof(f409,plain,
    ( v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_31 ),
    inference(superposition,[],[f89,f402])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f403,plain,
    ( spl6_31
    | ~ spl6_6
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f326,f309,f215,f129,f400])).

fof(f215,plain,
    ( spl6_18
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f309,plain,
    ( spl6_24
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f326,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl6_6
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(backward_demodulation,[],[f217,f317])).

fof(f317,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(resolution,[],[f310,f131])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f309])).

fof(f217,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f215])).

fof(f360,plain,
    ( spl6_28
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f344,f114,f109,f104,f358])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f343,f106])).

fof(f343,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0)))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f341,f116])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0)))
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f335,f111])).

fof(f335,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f334,f88])).

fof(f334,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f333,f89])).

fof(f333,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f332,f90])).

fof(f332,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f100,f72])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(k9_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_tmap_1(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2)))
        & u1_struct_0(X1) = sK5(X0,X1,X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f331,plain,
    ( spl6_25
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f317,f309,f129,f328])).

fof(f311,plain,
    ( spl6_24
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f293,f114,f109,f104,f309])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f292,f106])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f290,f116])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f276,f111])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f275,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f275,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f274,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f274,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f273,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f273,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f98,f72])).

% (3453)Refutation not found, incomplete strategy% (3453)------------------------------
% (3453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3453)Termination reason: Refutation not found, incomplete strategy

% (3453)Memory used [KB]: 10618
% (3453)Time elapsed: 0.136 s
% (3453)------------------------------
% (3453)------------------------------
fof(f98,plain,(
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
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK4(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK4(X0,X1,X2)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f218,plain,
    ( spl6_18
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f209,f206,f129,f215])).

fof(f206,plain,
    ( spl6_17
  <=> ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f209,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl6_6
    | ~ spl6_17 ),
    inference(resolution,[],[f207,f131])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f206])).

fof(f208,plain,
    ( spl6_17
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f203,f114,f109,f104,f206])).

fof(f203,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f202,f106])).

fof(f202,plain,
    ( ! [X0] :
        ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f200,f116])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f196,f111])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f82,f72])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f194,plain,
    ( spl6_16
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f187,f162,f157,f139,f191])).

fof(f139,plain,
    ( spl6_8
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f187,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f186,f164])).

fof(f186,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f185,f159])).

fof(f185,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f184,f141])).

fof(f141,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f155,f70])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f94,f70])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f183,plain,(
    ~ spl6_15 ),
    inference(avatar_split_clause,[],[f67,f180])).

fof(f67,plain,(
    ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f46,f45,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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

% (3459)Refutation not found, incomplete strategy% (3459)------------------------------
% (3459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f45,plain,
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

% (3459)Termination reason: Refutation not found, incomplete strategy

% (3459)Memory used [KB]: 10618
% (3459)Time elapsed: 0.143 s
% (3459)------------------------------
% (3459)------------------------------
fof(f46,plain,
    ( ? [X3] :
        ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f165,plain,
    ( spl6_12
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f154,f150,f134,f162])).

fof(f150,plain,
    ( spl6_10
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f154,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(resolution,[],[f151,f136])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f160,plain,
    ( spl6_11
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f153,f150,f129,f157])).

fof(f153,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(resolution,[],[f151,f131])).

fof(f152,plain,
    ( spl6_10
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f148,f114,f150])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl6_3 ),
    inference(resolution,[],[f71,f116])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f147,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f66,f144])).

fof(f66,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f142,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f65,f139])).

fof(f65,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f64,f134])).

fof(f64,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f132,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f62,f129])).

fof(f62,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f127,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f63,f124])).

fof(f63,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f117,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f60,f114])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f112,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f59,f109])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f58,f104])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (3455)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (3464)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (3457)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (3456)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (3459)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (3453)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.55  % (3464)Refutation not found, incomplete strategy% (3464)------------------------------
% 0.21/0.55  % (3464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3464)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3464)Memory used [KB]: 10746
% 0.21/0.55  % (3464)Time elapsed: 0.118 s
% 0.21/0.55  % (3464)------------------------------
% 0.21/0.55  % (3464)------------------------------
% 1.35/0.55  % (3471)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.35/0.56  % (3458)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.35/0.56  % (3454)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.56  % (3455)Refutation found. Thanks to Tanya!
% 1.35/0.56  % SZS status Theorem for theBenchmark
% 1.35/0.56  % SZS output start Proof for theBenchmark
% 1.35/0.56  fof(f992,plain,(
% 1.35/0.56    $false),
% 1.35/0.56    inference(avatar_sat_refutation,[],[f107,f112,f117,f127,f132,f137,f142,f147,f152,f160,f165,f183,f194,f208,f218,f311,f331,f360,f403,f533,f574,f587,f627,f633,f652,f692,f733,f775,f857,f907,f915,f952,f961,f977,f982,f991])).
% 1.35/0.56  fof(f991,plain,(
% 1.35/0.56    ~spl6_11 | spl6_86),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f990])).
% 1.35/0.56  fof(f990,plain,(
% 1.35/0.56    $false | (~spl6_11 | spl6_86)),
% 1.35/0.56    inference(subsumption_resolution,[],[f988,f159])).
% 1.35/0.56  fof(f159,plain,(
% 1.35/0.56    l1_pre_topc(sK1) | ~spl6_11),
% 1.35/0.56    inference(avatar_component_clause,[],[f157])).
% 1.35/0.56  fof(f157,plain,(
% 1.35/0.56    spl6_11 <=> l1_pre_topc(sK1)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.35/0.56  fof(f988,plain,(
% 1.35/0.56    ~l1_pre_topc(sK1) | spl6_86),
% 1.35/0.56    inference(resolution,[],[f976,f70])).
% 1.35/0.56  fof(f70,plain,(
% 1.35/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f20])).
% 1.35/0.56  fof(f20,plain,(
% 1.35/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f1])).
% 1.35/0.56  fof(f1,axiom,(
% 1.35/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.35/0.56  fof(f976,plain,(
% 1.35/0.56    ~l1_struct_0(sK1) | spl6_86),
% 1.35/0.56    inference(avatar_component_clause,[],[f974])).
% 1.35/0.56  fof(f974,plain,(
% 1.35/0.56    spl6_86 <=> l1_struct_0(sK1)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).
% 1.35/0.56  fof(f982,plain,(
% 1.35/0.56    ~spl6_12 | spl6_85),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f981])).
% 1.35/0.56  fof(f981,plain,(
% 1.35/0.56    $false | (~spl6_12 | spl6_85)),
% 1.35/0.56    inference(subsumption_resolution,[],[f979,f164])).
% 1.35/0.56  fof(f164,plain,(
% 1.35/0.56    l1_pre_topc(sK2) | ~spl6_12),
% 1.35/0.56    inference(avatar_component_clause,[],[f162])).
% 1.35/0.56  fof(f162,plain,(
% 1.35/0.56    spl6_12 <=> l1_pre_topc(sK2)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.35/0.56  % (3473)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.35/0.56  fof(f979,plain,(
% 1.35/0.56    ~l1_pre_topc(sK2) | spl6_85),
% 1.35/0.56    inference(resolution,[],[f972,f70])).
% 1.35/0.56  fof(f972,plain,(
% 1.35/0.56    ~l1_struct_0(sK2) | spl6_85),
% 1.35/0.56    inference(avatar_component_clause,[],[f970])).
% 1.35/0.56  fof(f970,plain,(
% 1.35/0.56    spl6_85 <=> l1_struct_0(sK2)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 1.35/0.56  fof(f977,plain,(
% 1.35/0.56    ~spl6_85 | ~spl6_86 | ~spl6_16 | spl6_83),
% 1.35/0.56    inference(avatar_split_clause,[],[f964,f958,f191,f974,f970])).
% 1.35/0.56  fof(f191,plain,(
% 1.35/0.56    spl6_16 <=> r1_tsep_1(sK2,sK1)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.35/0.56  fof(f958,plain,(
% 1.35/0.56    spl6_83 <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 1.35/0.56  fof(f964,plain,(
% 1.35/0.56    ~l1_struct_0(sK1) | ~l1_struct_0(sK2) | (~spl6_16 | spl6_83)),
% 1.35/0.56    inference(subsumption_resolution,[],[f963,f193])).
% 1.35/0.56  fof(f193,plain,(
% 1.35/0.56    r1_tsep_1(sK2,sK1) | ~spl6_16),
% 1.35/0.56    inference(avatar_component_clause,[],[f191])).
% 1.35/0.56  fof(f963,plain,(
% 1.35/0.56    ~r1_tsep_1(sK2,sK1) | ~l1_struct_0(sK1) | ~l1_struct_0(sK2) | spl6_83),
% 1.35/0.56    inference(resolution,[],[f960,f68])).
% 1.35/0.56  fof(f68,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f48])).
% 1.35/0.56  fof(f48,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.35/0.56    inference(nnf_transformation,[],[f19])).
% 1.35/0.56  fof(f19,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f7])).
% 1.35/0.56  fof(f7,axiom,(
% 1.35/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 1.35/0.56  fof(f960,plain,(
% 1.35/0.56    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | spl6_83),
% 1.35/0.56    inference(avatar_component_clause,[],[f958])).
% 1.35/0.56  fof(f961,plain,(
% 1.35/0.56    ~spl6_83 | spl6_5 | ~spl6_7 | ~spl6_9 | spl6_15 | ~spl6_82),
% 1.35/0.56    inference(avatar_split_clause,[],[f956,f950,f180,f144,f134,f124,f958])).
% 1.35/0.56  fof(f124,plain,(
% 1.35/0.56    spl6_5 <=> v2_struct_0(sK2)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.35/0.56  fof(f134,plain,(
% 1.35/0.56    spl6_7 <=> m1_pre_topc(sK2,sK0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.35/0.56  fof(f144,plain,(
% 1.35/0.56    spl6_9 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.35/0.56  fof(f180,plain,(
% 1.35/0.56    spl6_15 <=> r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.35/0.56  fof(f950,plain,(
% 1.35/0.56    spl6_82 <=> ! [X1,X0] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).
% 1.35/0.56  fof(f956,plain,(
% 1.35/0.56    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | (spl6_5 | ~spl6_7 | ~spl6_9 | spl6_15 | ~spl6_82)),
% 1.35/0.56    inference(subsumption_resolution,[],[f955,f126])).
% 1.35/0.56  fof(f126,plain,(
% 1.35/0.56    ~v2_struct_0(sK2) | spl6_5),
% 1.35/0.56    inference(avatar_component_clause,[],[f124])).
% 1.35/0.56  fof(f955,plain,(
% 1.35/0.56    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | v2_struct_0(sK2) | (~spl6_7 | ~spl6_9 | spl6_15 | ~spl6_82)),
% 1.35/0.56    inference(subsumption_resolution,[],[f954,f136])).
% 1.35/0.56  fof(f136,plain,(
% 1.35/0.56    m1_pre_topc(sK2,sK0) | ~spl6_7),
% 1.35/0.56    inference(avatar_component_clause,[],[f134])).
% 1.35/0.56  fof(f954,plain,(
% 1.35/0.56    ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (~spl6_9 | spl6_15 | ~spl6_82)),
% 1.35/0.56    inference(subsumption_resolution,[],[f953,f146])).
% 1.35/0.56  fof(f146,plain,(
% 1.35/0.56    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl6_9),
% 1.35/0.56    inference(avatar_component_clause,[],[f144])).
% 1.35/0.56  fof(f953,plain,(
% 1.35/0.56    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | (spl6_15 | ~spl6_82)),
% 1.35/0.56    inference(resolution,[],[f951,f182])).
% 1.35/0.56  fof(f182,plain,(
% 1.35/0.56    ~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) | spl6_15),
% 1.35/0.56    inference(avatar_component_clause,[],[f180])).
% 1.35/0.56  fof(f951,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl6_82),
% 1.35/0.56    inference(avatar_component_clause,[],[f950])).
% 1.35/0.56  fof(f952,plain,(
% 1.35/0.56    spl6_82 | ~spl6_63 | ~spl6_80),
% 1.35/0.56    inference(avatar_split_clause,[],[f916,f904,f731,f950])).
% 1.35/0.56  fof(f731,plain,(
% 1.35/0.56    spl6_63 <=> ! [X1,X0] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 1.35/0.56  fof(f904,plain,(
% 1.35/0.56    spl6_80 <=> k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 1.35/0.56  fof(f916,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (~spl6_63 | ~spl6_80)),
% 1.35/0.56    inference(backward_demodulation,[],[f732,f906])).
% 1.35/0.56  fof(f906,plain,(
% 1.35/0.56    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_80),
% 1.35/0.56    inference(avatar_component_clause,[],[f904])).
% 1.35/0.56  fof(f732,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl6_63),
% 1.35/0.56    inference(avatar_component_clause,[],[f731])).
% 1.35/0.56  fof(f915,plain,(
% 1.35/0.56    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_79),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f914])).
% 1.35/0.56  fof(f914,plain,(
% 1.35/0.56    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_79)),
% 1.35/0.56    inference(subsumption_resolution,[],[f913,f106])).
% 1.35/0.56  fof(f106,plain,(
% 1.35/0.56    ~v2_struct_0(sK0) | spl6_1),
% 1.35/0.56    inference(avatar_component_clause,[],[f104])).
% 1.35/0.56  fof(f104,plain,(
% 1.35/0.56    spl6_1 <=> v2_struct_0(sK0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.35/0.56  fof(f913,plain,(
% 1.35/0.56    v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_6 | spl6_79)),
% 1.35/0.56    inference(subsumption_resolution,[],[f912,f111])).
% 1.35/0.56  fof(f111,plain,(
% 1.35/0.56    v2_pre_topc(sK0) | ~spl6_2),
% 1.35/0.56    inference(avatar_component_clause,[],[f109])).
% 1.35/0.56  fof(f109,plain,(
% 1.35/0.56    spl6_2 <=> v2_pre_topc(sK0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.35/0.56  fof(f912,plain,(
% 1.35/0.56    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_6 | spl6_79)),
% 1.35/0.56    inference(subsumption_resolution,[],[f911,f116])).
% 1.35/0.56  fof(f116,plain,(
% 1.35/0.56    l1_pre_topc(sK0) | ~spl6_3),
% 1.35/0.56    inference(avatar_component_clause,[],[f114])).
% 1.35/0.56  fof(f114,plain,(
% 1.35/0.56    spl6_3 <=> l1_pre_topc(sK0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.35/0.56  fof(f911,plain,(
% 1.35/0.56    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | spl6_79)),
% 1.35/0.56    inference(subsumption_resolution,[],[f909,f131])).
% 1.35/0.56  fof(f131,plain,(
% 1.35/0.56    m1_pre_topc(sK1,sK0) | ~spl6_6),
% 1.35/0.56    inference(avatar_component_clause,[],[f129])).
% 1.35/0.56  fof(f129,plain,(
% 1.35/0.56    spl6_6 <=> m1_pre_topc(sK1,sK0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.35/0.56  fof(f909,plain,(
% 1.35/0.56    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl6_79),
% 1.35/0.56    inference(resolution,[],[f902,f88])).
% 1.35/0.56  fof(f88,plain,(
% 1.35/0.56    ( ! [X0,X1] : (v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f36])).
% 1.35/0.56  fof(f36,plain,(
% 1.35/0.56    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f35])).
% 1.35/0.56  fof(f35,plain,(
% 1.35/0.56    ! [X0,X1] : ((m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f10])).
% 1.35/0.56  fof(f10,axiom,(
% 1.35/0.56    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k9_tmap_1(X0,X1))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).
% 1.35/0.56  fof(f902,plain,(
% 1.35/0.56    ~v1_funct_1(k9_tmap_1(sK0,sK1)) | spl6_79),
% 1.35/0.56    inference(avatar_component_clause,[],[f900])).
% 1.35/0.56  fof(f900,plain,(
% 1.35/0.56    spl6_79 <=> v1_funct_1(k9_tmap_1(sK0,sK1))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 1.35/0.56  fof(f907,plain,(
% 1.35/0.56    ~spl6_79 | spl6_80 | spl6_22 | ~spl6_36 | ~spl6_42 | ~spl6_44 | ~spl6_51 | ~spl6_52 | ~spl6_56),
% 1.35/0.56    inference(avatar_split_clause,[],[f898,f689,f649,f624,f584,f571,f530,f286,f904,f900])).
% 1.35/0.56  fof(f286,plain,(
% 1.35/0.56    spl6_22 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.35/0.56  fof(f530,plain,(
% 1.35/0.56    spl6_36 <=> v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.35/0.56  fof(f571,plain,(
% 1.35/0.56    spl6_42 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 1.35/0.56  fof(f584,plain,(
% 1.35/0.56    spl6_44 <=> m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 1.35/0.56  fof(f624,plain,(
% 1.35/0.56    spl6_51 <=> v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 1.35/0.56  fof(f649,plain,(
% 1.35/0.56    spl6_52 <=> v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 1.35/0.56  fof(f689,plain,(
% 1.35/0.56    spl6_56 <=> m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 1.35/0.56  fof(f898,plain,(
% 1.35/0.56    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | (spl6_22 | ~spl6_36 | ~spl6_42 | ~spl6_44 | ~spl6_51 | ~spl6_52 | ~spl6_56)),
% 1.35/0.56    inference(subsumption_resolution,[],[f847,f288])).
% 1.35/0.56  fof(f288,plain,(
% 1.35/0.56    ~v1_xboole_0(u1_struct_0(sK0)) | spl6_22),
% 1.35/0.56    inference(avatar_component_clause,[],[f286])).
% 1.35/0.56  fof(f847,plain,(
% 1.35/0.56    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl6_36 | ~spl6_42 | ~spl6_44 | ~spl6_51 | ~spl6_52 | ~spl6_56)),
% 1.35/0.56    inference(subsumption_resolution,[],[f846,f586])).
% 1.35/0.56  fof(f586,plain,(
% 1.35/0.56    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl6_44),
% 1.35/0.56    inference(avatar_component_clause,[],[f584])).
% 1.35/0.56  fof(f846,plain,(
% 1.35/0.56    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl6_36 | ~spl6_42 | ~spl6_51 | ~spl6_52 | ~spl6_56)),
% 1.35/0.56    inference(subsumption_resolution,[],[f845,f651])).
% 1.35/0.56  % (3461)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.35/0.56  fof(f651,plain,(
% 1.35/0.56    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~spl6_52),
% 1.35/0.56    inference(avatar_component_clause,[],[f649])).
% 1.35/0.56  fof(f845,plain,(
% 1.35/0.56    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl6_36 | ~spl6_42 | ~spl6_51 | ~spl6_56)),
% 1.35/0.56    inference(subsumption_resolution,[],[f844,f626])).
% 1.35/0.56  fof(f626,plain,(
% 1.35/0.56    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl6_51),
% 1.35/0.56    inference(avatar_component_clause,[],[f624])).
% 1.35/0.56  fof(f844,plain,(
% 1.35/0.56    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl6_36 | ~spl6_42 | ~spl6_56)),
% 1.35/0.56    inference(subsumption_resolution,[],[f577,f691])).
% 1.35/0.56  fof(f691,plain,(
% 1.35/0.56    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl6_56),
% 1.35/0.56    inference(avatar_component_clause,[],[f689])).
% 1.35/0.56  fof(f577,plain,(
% 1.35/0.56    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl6_36 | ~spl6_42)),
% 1.35/0.56    inference(subsumption_resolution,[],[f576,f532])).
% 1.35/0.56  fof(f532,plain,(
% 1.35/0.56    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl6_36),
% 1.35/0.56    inference(avatar_component_clause,[],[f530])).
% 1.35/0.56  fof(f576,plain,(
% 1.35/0.56    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl6_42),
% 1.35/0.56    inference(duplicate_literal_removal,[],[f575])).
% 1.35/0.56  fof(f575,plain,(
% 1.35/0.56    k9_tmap_1(sK0,sK1) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k9_tmap_1(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl6_42),
% 1.35/0.56    inference(resolution,[],[f573,f95])).
% 1.35/0.56  fof(f95,plain,(
% 1.35/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f57])).
% 1.35/0.56  fof(f57,plain,(
% 1.35/0.56    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.35/0.56    inference(nnf_transformation,[],[f42])).
% 1.35/0.56  fof(f42,plain,(
% 1.35/0.56    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.35/0.56    inference(flattening,[],[f41])).
% 1.35/0.56  fof(f41,plain,(
% 1.35/0.56    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.35/0.56    inference(ennf_transformation,[],[f4])).
% 1.35/0.56  fof(f4,axiom,(
% 1.35/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 1.35/0.56  fof(f573,plain,(
% 1.35/0.56    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | ~spl6_42),
% 1.35/0.56    inference(avatar_component_clause,[],[f571])).
% 1.35/0.56  fof(f857,plain,(
% 1.35/0.56    spl6_1 | ~spl6_22 | ~spl6_69),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f856])).
% 1.35/0.56  fof(f856,plain,(
% 1.35/0.56    $false | (spl6_1 | ~spl6_22 | ~spl6_69)),
% 1.35/0.56    inference(subsumption_resolution,[],[f855,f106])).
% 1.35/0.56  fof(f855,plain,(
% 1.35/0.56    v2_struct_0(sK0) | (~spl6_22 | ~spl6_69)),
% 1.35/0.56    inference(subsumption_resolution,[],[f853,f760])).
% 1.35/0.56  fof(f760,plain,(
% 1.35/0.56    l1_struct_0(sK0) | ~spl6_69),
% 1.35/0.56    inference(avatar_component_clause,[],[f759])).
% 1.35/0.56  fof(f759,plain,(
% 1.35/0.56    spl6_69 <=> l1_struct_0(sK0)),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 1.35/0.56  fof(f853,plain,(
% 1.35/0.56    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_22),
% 1.35/0.56    inference(resolution,[],[f287,f73])).
% 1.35/0.56  fof(f73,plain,(
% 1.35/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f24])).
% 1.35/0.56  fof(f24,plain,(
% 1.35/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f23])).
% 1.35/0.56  fof(f23,plain,(
% 1.35/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f3])).
% 1.35/0.56  fof(f3,axiom,(
% 1.35/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.35/0.56  fof(f287,plain,(
% 1.35/0.56    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_22),
% 1.35/0.56    inference(avatar_component_clause,[],[f286])).
% 1.35/0.56  fof(f775,plain,(
% 1.35/0.56    ~spl6_3 | spl6_69),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f774])).
% 1.35/0.56  fof(f774,plain,(
% 1.35/0.56    $false | (~spl6_3 | spl6_69)),
% 1.35/0.56    inference(subsumption_resolution,[],[f772,f116])).
% 1.35/0.56  fof(f772,plain,(
% 1.35/0.56    ~l1_pre_topc(sK0) | spl6_69),
% 1.35/0.56    inference(resolution,[],[f761,f70])).
% 1.35/0.56  fof(f761,plain,(
% 1.35/0.56    ~l1_struct_0(sK0) | spl6_69),
% 1.35/0.56    inference(avatar_component_clause,[],[f759])).
% 1.35/0.56  fof(f733,plain,(
% 1.35/0.56    spl6_63 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_50),
% 1.35/0.56    inference(avatar_split_clause,[],[f725,f620,f328,f114,f109,f104,f731])).
% 1.35/0.56  fof(f328,plain,(
% 1.35/0.56    spl6_25 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.35/0.56  fof(f620,plain,(
% 1.35/0.56    spl6_50 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 1.35/0.56  fof(f725,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_50)),
% 1.35/0.56    inference(subsumption_resolution,[],[f506,f621])).
% 1.35/0.56  fof(f621,plain,(
% 1.35/0.56    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_50),
% 1.35/0.56    inference(avatar_component_clause,[],[f620])).
% 1.35/0.56  fof(f506,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25)),
% 1.35/0.56    inference(subsumption_resolution,[],[f505,f106])).
% 1.35/0.56  fof(f505,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_25)),
% 1.35/0.56    inference(subsumption_resolution,[],[f504,f111])).
% 1.35/0.56  fof(f504,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl6_3 | ~spl6_25)),
% 1.35/0.56    inference(subsumption_resolution,[],[f501,f116])).
% 1.35/0.56  fof(f501,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_tmap_1(X0,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl6_25),
% 1.35/0.56    inference(superposition,[],[f84,f330])).
% 1.35/0.56  fof(f330,plain,(
% 1.35/0.56    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl6_25),
% 1.35/0.56    inference(avatar_component_clause,[],[f328])).
% 1.35/0.56  fof(f84,plain,(
% 1.35/0.56    ( ! [X2,X0,X3,X1] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f32])).
% 1.35/0.56  fof(f32,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f31])).
% 1.35/0.56  fof(f31,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X3,u1_struct_0(X2))) | ~r1_xboole_0(u1_struct_0(X2),X1)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f13])).
% 1.35/0.56  fof(f13,axiom,(
% 1.35/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).
% 1.35/0.56  fof(f692,plain,(
% 1.35/0.56    spl6_56 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_31 | ~spl6_50),
% 1.35/0.56    inference(avatar_split_clause,[],[f687,f620,f400,f328,f114,f109,f104,f689])).
% 1.35/0.56  fof(f400,plain,(
% 1.35/0.56    spl6_31 <=> u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.35/0.56  fof(f687,plain,(
% 1.35/0.56    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_31 | ~spl6_50)),
% 1.35/0.56    inference(subsumption_resolution,[],[f510,f621])).
% 1.35/0.56  fof(f510,plain,(
% 1.35/0.56    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_31)),
% 1.35/0.56    inference(forward_demodulation,[],[f509,f402])).
% 1.35/0.56  fof(f402,plain,(
% 1.35/0.56    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl6_31),
% 1.35/0.56    inference(avatar_component_clause,[],[f400])).
% 1.35/0.56  fof(f509,plain,(
% 1.35/0.56    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25)),
% 1.35/0.56    inference(subsumption_resolution,[],[f508,f106])).
% 1.35/0.56  fof(f508,plain,(
% 1.35/0.56    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_25)),
% 1.35/0.56    inference(subsumption_resolution,[],[f507,f111])).
% 1.35/0.56  fof(f507,plain,(
% 1.35/0.56    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_25)),
% 1.35/0.56    inference(subsumption_resolution,[],[f502,f116])).
% 1.35/0.56  fof(f502,plain,(
% 1.35/0.56    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_25),
% 1.35/0.56    inference(superposition,[],[f93,f330])).
% 1.35/0.56  fof(f93,plain,(
% 1.35/0.56    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f38])).
% 1.35/0.56  fof(f38,plain,(
% 1.35/0.56    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f37])).
% 1.35/0.56  fof(f37,plain,(
% 1.35/0.56    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f8])).
% 1.35/0.56  fof(f8,axiom,(
% 1.35/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.35/0.56  fof(f652,plain,(
% 1.35/0.56    spl6_52 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_50),
% 1.35/0.56    inference(avatar_split_clause,[],[f647,f620,f114,f109,f104,f649])).
% 1.35/0.56  fof(f647,plain,(
% 1.35/0.56    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_50)),
% 1.35/0.56    inference(subsumption_resolution,[],[f646,f106])).
% 1.35/0.56  fof(f646,plain,(
% 1.35/0.56    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_50)),
% 1.35/0.56    inference(subsumption_resolution,[],[f645,f111])).
% 1.35/0.56  fof(f645,plain,(
% 1.35/0.56    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_50)),
% 1.35/0.56    inference(subsumption_resolution,[],[f636,f116])).
% 1.35/0.56  fof(f636,plain,(
% 1.35/0.56    v1_funct_1(k7_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_50),
% 1.35/0.56    inference(resolution,[],[f621,f91])).
% 1.35/0.56  fof(f91,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f38])).
% 1.35/0.56  fof(f633,plain,(
% 1.35/0.56    ~spl6_3 | ~spl6_6 | spl6_50),
% 1.35/0.56    inference(avatar_contradiction_clause,[],[f632])).
% 1.35/0.56  fof(f632,plain,(
% 1.35/0.56    $false | (~spl6_3 | ~spl6_6 | spl6_50)),
% 1.35/0.56    inference(subsumption_resolution,[],[f631,f116])).
% 1.35/0.56  fof(f631,plain,(
% 1.35/0.56    ~l1_pre_topc(sK0) | (~spl6_6 | spl6_50)),
% 1.35/0.56    inference(subsumption_resolution,[],[f629,f131])).
% 1.35/0.56  fof(f629,plain,(
% 1.35/0.56    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl6_50),
% 1.35/0.56    inference(resolution,[],[f622,f72])).
% 1.35/0.56  fof(f72,plain,(
% 1.35/0.56    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f22])).
% 1.35/0.56  fof(f22,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.35/0.56    inference(ennf_transformation,[],[f14])).
% 1.35/0.56  fof(f14,axiom,(
% 1.35/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.35/0.56  fof(f622,plain,(
% 1.35/0.56    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_50),
% 1.35/0.56    inference(avatar_component_clause,[],[f620])).
% 1.35/0.56  fof(f627,plain,(
% 1.35/0.56    ~spl6_50 | spl6_51 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_31),
% 1.35/0.56    inference(avatar_split_clause,[],[f514,f400,f328,f114,f109,f104,f624,f620])).
% 1.35/0.56  fof(f514,plain,(
% 1.35/0.56    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25 | ~spl6_31)),
% 1.35/0.56    inference(forward_demodulation,[],[f513,f402])).
% 1.35/0.56  fof(f513,plain,(
% 1.35/0.56    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_25)),
% 1.35/0.56    inference(subsumption_resolution,[],[f512,f106])).
% 1.35/0.56  fof(f512,plain,(
% 1.35/0.56    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_25)),
% 1.35/0.56    inference(subsumption_resolution,[],[f511,f111])).
% 1.35/0.56  fof(f511,plain,(
% 1.35/0.56    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_25)),
% 1.35/0.56    inference(subsumption_resolution,[],[f503,f116])).
% 1.35/0.56  fof(f503,plain,(
% 1.35/0.56    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_25),
% 1.35/0.56    inference(superposition,[],[f92,f330])).
% 1.35/0.56  fof(f92,plain,(
% 1.35/0.56    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f38])).
% 1.35/0.56  fof(f587,plain,(
% 1.35/0.56    spl6_44 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_31),
% 1.35/0.56    inference(avatar_split_clause,[],[f430,f400,f129,f114,f109,f104,f584])).
% 1.35/0.56  fof(f430,plain,(
% 1.35/0.56    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_31)),
% 1.35/0.56    inference(subsumption_resolution,[],[f429,f106])).
% 1.35/0.56  fof(f429,plain,(
% 1.35/0.56    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_31)),
% 1.35/0.56    inference(subsumption_resolution,[],[f428,f111])).
% 1.35/0.56  fof(f428,plain,(
% 1.35/0.56    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_6 | ~spl6_31)),
% 1.35/0.56    inference(subsumption_resolution,[],[f427,f116])).
% 1.35/0.56  fof(f427,plain,(
% 1.35/0.56    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_31)),
% 1.35/0.56    inference(subsumption_resolution,[],[f408,f131])).
% 1.35/0.56  fof(f408,plain,(
% 1.35/0.56    m1_subset_1(k9_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_31),
% 1.35/0.56    inference(superposition,[],[f90,f402])).
% 1.35/0.56  fof(f90,plain,(
% 1.35/0.56    ( ! [X0,X1] : (m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f36])).
% 1.35/0.56  fof(f574,plain,(
% 1.35/0.56    spl6_42 | ~spl6_6 | ~spl6_25 | ~spl6_28 | ~spl6_31),
% 1.35/0.56    inference(avatar_split_clause,[],[f564,f400,f358,f328,f129,f571])).
% 1.35/0.56  fof(f358,plain,(
% 1.35/0.56    spl6_28 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0))))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 1.35/0.56  fof(f564,plain,(
% 1.35/0.56    r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | (~spl6_6 | ~spl6_25 | ~spl6_28 | ~spl6_31)),
% 1.35/0.56    inference(forward_demodulation,[],[f563,f402])).
% 1.35/0.56  fof(f563,plain,(
% 1.35/0.56    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | (~spl6_6 | ~spl6_25 | ~spl6_28)),
% 1.35/0.56    inference(forward_demodulation,[],[f362,f330])).
% 1.35/0.56  fof(f362,plain,(
% 1.35/0.56    r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k9_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1))) | (~spl6_6 | ~spl6_28)),
% 1.35/0.56    inference(resolution,[],[f359,f131])).
% 1.35/0.56  fof(f359,plain,(
% 1.35/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0)))) ) | ~spl6_28),
% 1.35/0.56    inference(avatar_component_clause,[],[f358])).
% 1.35/0.56  fof(f533,plain,(
% 1.35/0.56    spl6_36 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_31),
% 1.35/0.56    inference(avatar_split_clause,[],[f434,f400,f129,f114,f109,f104,f530])).
% 1.35/0.56  fof(f434,plain,(
% 1.35/0.56    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_31)),
% 1.35/0.56    inference(subsumption_resolution,[],[f433,f106])).
% 1.35/0.56  fof(f433,plain,(
% 1.35/0.56    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_31)),
% 1.35/0.56    inference(subsumption_resolution,[],[f432,f111])).
% 1.35/0.56  fof(f432,plain,(
% 1.35/0.56    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_3 | ~spl6_6 | ~spl6_31)),
% 1.35/0.56    inference(subsumption_resolution,[],[f431,f116])).
% 1.35/0.56  fof(f431,plain,(
% 1.35/0.56    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_31)),
% 1.35/0.56    inference(subsumption_resolution,[],[f409,f131])).
% 1.35/0.56  fof(f409,plain,(
% 1.35/0.56    v1_funct_2(k9_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl6_31),
% 1.35/0.56    inference(superposition,[],[f89,f402])).
% 1.35/0.56  fof(f89,plain,(
% 1.35/0.56    ( ! [X0,X1] : (v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f36])).
% 1.35/0.56  fof(f403,plain,(
% 1.35/0.56    spl6_31 | ~spl6_6 | ~spl6_18 | ~spl6_24),
% 1.35/0.56    inference(avatar_split_clause,[],[f326,f309,f215,f129,f400])).
% 1.35/0.56  fof(f215,plain,(
% 1.35/0.56    spl6_18 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.35/0.56  fof(f309,plain,(
% 1.35/0.56    spl6_24 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0))),
% 1.35/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.35/0.56  fof(f326,plain,(
% 1.35/0.56    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (~spl6_6 | ~spl6_18 | ~spl6_24)),
% 1.35/0.56    inference(backward_demodulation,[],[f217,f317])).
% 1.35/0.56  fof(f317,plain,(
% 1.35/0.56    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (~spl6_6 | ~spl6_24)),
% 1.35/0.56    inference(resolution,[],[f310,f131])).
% 1.35/0.56  fof(f310,plain,(
% 1.35/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0)) ) | ~spl6_24),
% 1.35/0.56    inference(avatar_component_clause,[],[f309])).
% 1.35/0.56  fof(f217,plain,(
% 1.35/0.56    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl6_18),
% 1.35/0.56    inference(avatar_component_clause,[],[f215])).
% 1.35/0.56  fof(f360,plain,(
% 1.35/0.56    spl6_28 | spl6_1 | ~spl6_2 | ~spl6_3),
% 1.35/0.56    inference(avatar_split_clause,[],[f344,f114,f109,f104,f358])).
% 1.35/0.56  fof(f344,plain,(
% 1.35/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.35/0.56    inference(subsumption_resolution,[],[f343,f106])).
% 1.35/0.56  fof(f343,plain,(
% 1.35/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0))) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3)),
% 1.35/0.56    inference(subsumption_resolution,[],[f341,f116])).
% 1.35/0.56  fof(f341,plain,(
% 1.35/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,X0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))),k9_tmap_1(sK0,X0),k7_tmap_1(sK0,u1_struct_0(X0))) | v2_struct_0(sK0)) ) | ~spl6_2),
% 1.35/0.56    inference(resolution,[],[f335,f111])).
% 1.35/0.56  fof(f335,plain,(
% 1.35/0.56    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f334,f88])).
% 1.35/0.56  fof(f334,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f333,f89])).
% 1.35/0.56  fof(f333,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f332,f90])).
% 1.35/0.56  fof(f332,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(subsumption_resolution,[],[f100,f72])).
% 1.35/0.56  fof(f100,plain,(
% 1.35/0.56    ( ! [X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),k9_tmap_1(X0,X1),k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(k9_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k9_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(equality_resolution,[],[f99])).
% 1.35/0.56  fof(f99,plain,(
% 1.35/0.56    ( ! [X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))),X2,k7_tmap_1(X0,u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(equality_resolution,[],[f78])).
% 1.35/0.56  fof(f78,plain,(
% 1.35/0.56    ( ! [X4,X2,X0,X1] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_tmap_1(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.56    inference(cnf_transformation,[],[f56])).
% 1.35/0.56  fof(f56,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) & u1_struct_0(X1) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f54,f55])).
% 1.35/0.56  fof(f55,plain,(
% 1.35/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK5(X0,X1,X2))),X2,k7_tmap_1(X0,sK5(X0,X1,X2))) & u1_struct_0(X1) = sK5(X0,X1,X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.35/0.56    introduced(choice_axiom,[])).
% 1.35/0.56  fof(f54,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(rectify,[],[f53])).
% 1.35/0.56  fof(f53,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(nnf_transformation,[],[f28])).
% 1.35/0.56  fof(f28,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.56    inference(flattening,[],[f27])).
% 1.35/0.56  fof(f27,plain,(
% 1.35/0.56    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.56    inference(ennf_transformation,[],[f6])).
% 1.35/0.56  fof(f6,axiom,(
% 1.35/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 1.35/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).
% 1.35/0.56  fof(f331,plain,(
% 1.35/0.56    spl6_25 | ~spl6_6 | ~spl6_24),
% 1.35/0.56    inference(avatar_split_clause,[],[f317,f309,f129,f328])).
% 1.35/0.56  fof(f311,plain,(
% 1.35/0.56    spl6_24 | spl6_1 | ~spl6_2 | ~spl6_3),
% 1.35/0.56    inference(avatar_split_clause,[],[f293,f114,f109,f104,f309])).
% 1.35/0.56  fof(f293,plain,(
% 1.35/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.35/0.56    inference(subsumption_resolution,[],[f292,f106])).
% 1.35/0.56  fof(f292,plain,(
% 1.35/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3)),
% 1.35/0.56    inference(subsumption_resolution,[],[f290,f116])).
% 1.35/0.56  fof(f290,plain,(
% 1.35/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | k6_tmap_1(sK0,u1_struct_0(X0)) = k8_tmap_1(sK0,X0) | v2_struct_0(sK0)) ) | ~spl6_2),
% 1.35/0.56    inference(resolution,[],[f276,f111])).
% 1.35/0.57  fof(f276,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(subsumption_resolution,[],[f275,f85])).
% 1.35/0.57  fof(f85,plain,(
% 1.35/0.57    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f34])).
% 1.35/0.57  fof(f34,plain,(
% 1.35/0.57    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.57    inference(flattening,[],[f33])).
% 1.35/0.57  fof(f33,plain,(
% 1.35/0.57    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f9])).
% 1.35/0.57  fof(f9,axiom,(
% 1.35/0.57    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 1.35/0.57  fof(f275,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(subsumption_resolution,[],[f274,f86])).
% 1.35/0.57  fof(f86,plain,(
% 1.35/0.57    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f34])).
% 1.35/0.57  fof(f274,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(subsumption_resolution,[],[f273,f87])).
% 1.35/0.57  fof(f87,plain,(
% 1.35/0.57    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f34])).
% 1.35/0.57  fof(f273,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(subsumption_resolution,[],[f98,f72])).
% 1.35/0.57  % (3453)Refutation not found, incomplete strategy% (3453)------------------------------
% 1.35/0.57  % (3453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (3453)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (3453)Memory used [KB]: 10618
% 1.35/0.57  % (3453)Time elapsed: 0.136 s
% 1.35/0.57  % (3453)------------------------------
% 1.35/0.57  % (3453)------------------------------
% 1.35/0.57  fof(f98,plain,(
% 1.35/0.57    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(equality_resolution,[],[f97])).
% 1.35/0.57  fof(f97,plain,(
% 1.35/0.57    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(equality_resolution,[],[f74])).
% 1.35/0.57  fof(f74,plain,(
% 1.35/0.57    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f52])).
% 1.35/0.57  fof(f52,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK4(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 1.35/0.57  fof(f51,plain,(
% 1.35/0.57    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK4(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK4(X0,X1,X2) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f50,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.57    inference(rectify,[],[f49])).
% 1.35/0.57  fof(f49,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.57    inference(nnf_transformation,[],[f26])).
% 1.35/0.57  fof(f26,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.57    inference(flattening,[],[f25])).
% 1.35/0.57  fof(f25,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f5])).
% 1.35/0.57  fof(f5,axiom,(
% 1.35/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).
% 1.35/0.57  fof(f218,plain,(
% 1.35/0.57    spl6_18 | ~spl6_6 | ~spl6_17),
% 1.35/0.57    inference(avatar_split_clause,[],[f209,f206,f129,f215])).
% 1.35/0.57  fof(f206,plain,(
% 1.35/0.57    spl6_17 <=> ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0))),
% 1.35/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.35/0.57  fof(f209,plain,(
% 1.35/0.57    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (~spl6_6 | ~spl6_17)),
% 1.35/0.57    inference(resolution,[],[f207,f131])).
% 1.35/0.57  fof(f207,plain,(
% 1.35/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0)))) ) | ~spl6_17),
% 1.35/0.57    inference(avatar_component_clause,[],[f206])).
% 1.35/0.57  fof(f208,plain,(
% 1.35/0.57    spl6_17 | spl6_1 | ~spl6_2 | ~spl6_3),
% 1.35/0.57    inference(avatar_split_clause,[],[f203,f114,f109,f104,f206])).
% 1.35/0.57  fof(f203,plain,(
% 1.35/0.57    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.35/0.57    inference(subsumption_resolution,[],[f202,f106])).
% 1.35/0.57  fof(f202,plain,(
% 1.35/0.57    ( ! [X0] : (u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0)) ) | (~spl6_2 | ~spl6_3)),
% 1.35/0.57    inference(subsumption_resolution,[],[f200,f116])).
% 1.35/0.57  fof(f200,plain,(
% 1.35/0.57    ( ! [X0] : (~l1_pre_topc(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(X0))) | v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0)) ) | ~spl6_2),
% 1.35/0.57    inference(resolution,[],[f196,f111])).
% 1.35/0.57  fof(f196,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)) )),
% 1.35/0.57    inference(duplicate_literal_removal,[],[f195])).
% 1.35/0.57  fof(f195,plain,(
% 1.35/0.57    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.35/0.57    inference(resolution,[],[f82,f72])).
% 1.35/0.57  fof(f82,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f30])).
% 1.35/0.57  fof(f30,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.35/0.57    inference(flattening,[],[f29])).
% 1.35/0.57  fof(f29,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f12])).
% 1.35/0.57  fof(f12,axiom,(
% 1.35/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.35/0.57  fof(f194,plain,(
% 1.35/0.57    spl6_16 | ~spl6_8 | ~spl6_11 | ~spl6_12),
% 1.35/0.57    inference(avatar_split_clause,[],[f187,f162,f157,f139,f191])).
% 1.35/0.57  fof(f139,plain,(
% 1.35/0.57    spl6_8 <=> r1_tsep_1(sK1,sK2)),
% 1.35/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.35/0.57  fof(f187,plain,(
% 1.35/0.57    r1_tsep_1(sK2,sK1) | (~spl6_8 | ~spl6_11 | ~spl6_12)),
% 1.35/0.57    inference(subsumption_resolution,[],[f186,f164])).
% 1.35/0.57  fof(f186,plain,(
% 1.35/0.57    r1_tsep_1(sK2,sK1) | ~l1_pre_topc(sK2) | (~spl6_8 | ~spl6_11)),
% 1.35/0.57    inference(subsumption_resolution,[],[f185,f159])).
% 1.35/0.57  fof(f185,plain,(
% 1.35/0.57    r1_tsep_1(sK2,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK2) | ~spl6_8),
% 1.35/0.57    inference(resolution,[],[f184,f141])).
% 1.35/0.57  fof(f141,plain,(
% 1.35/0.57    r1_tsep_1(sK1,sK2) | ~spl6_8),
% 1.35/0.57    inference(avatar_component_clause,[],[f139])).
% 1.35/0.57  fof(f184,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 1.35/0.57    inference(resolution,[],[f155,f70])).
% 1.35/0.57  fof(f155,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.35/0.57    inference(resolution,[],[f94,f70])).
% 1.35/0.57  fof(f94,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | r1_tsep_1(X1,X0)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f40])).
% 1.35/0.57  fof(f40,plain,(
% 1.35/0.57    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.35/0.57    inference(flattening,[],[f39])).
% 1.35/0.57  fof(f39,plain,(
% 1.35/0.57    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f11])).
% 1.35/0.57  fof(f11,axiom,(
% 1.35/0.57    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 1.35/0.57  fof(f183,plain,(
% 1.35/0.57    ~spl6_15),
% 1.35/0.57    inference(avatar_split_clause,[],[f67,f180])).
% 1.35/0.57  fof(f67,plain,(
% 1.35/0.57    ~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3)),
% 1.35/0.57    inference(cnf_transformation,[],[f47])).
% 1.35/0.57  fof(f47,plain,(
% 1.35/0.57    (((~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2))) & r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.35/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f46,f45,f44,f43])).
% 1.35/0.57  fof(f43,plain,(
% 1.35/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f44,plain,(
% 1.35/0.57    ? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK0,X1),k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  % (3459)Refutation not found, incomplete strategy% (3459)------------------------------
% 1.35/0.57  % (3459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  fof(f45,plain,(
% 1.35/0.57    ? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) & r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  % (3459)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (3459)Memory used [KB]: 10618
% 1.35/0.57  % (3459)Time elapsed: 0.143 s
% 1.35/0.57  % (3459)------------------------------
% 1.35/0.57  % (3459)------------------------------
% 1.35/0.57  fof(f46,plain,(
% 1.35/0.57    ? [X3] : (~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),X3) & m1_subset_1(X3,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,k8_tmap_1(sK0,sK1),k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK2),sK3) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.35/0.57    introduced(choice_axiom,[])).
% 1.35/0.57  fof(f18,plain,(
% 1.35/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.35/0.57    inference(flattening,[],[f17])).
% 1.35/0.57  fof(f17,plain,(
% 1.35/0.57    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.35/0.57    inference(ennf_transformation,[],[f16])).
% 1.35/0.57  fof(f16,negated_conjecture,(
% 1.35/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 1.35/0.57    inference(negated_conjecture,[],[f15])).
% 1.35/0.57  fof(f15,conjecture,(
% 1.35/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tsep_1(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k8_tmap_1(X0,X1),k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X2),X3))))))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_tmap_1)).
% 1.35/0.57  fof(f165,plain,(
% 1.35/0.57    spl6_12 | ~spl6_7 | ~spl6_10),
% 1.35/0.57    inference(avatar_split_clause,[],[f154,f150,f134,f162])).
% 1.35/0.57  fof(f150,plain,(
% 1.35/0.57    spl6_10 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))),
% 1.35/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.35/0.57  fof(f154,plain,(
% 1.35/0.57    l1_pre_topc(sK2) | (~spl6_7 | ~spl6_10)),
% 1.35/0.57    inference(resolution,[],[f151,f136])).
% 1.35/0.57  fof(f151,plain,(
% 1.35/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl6_10),
% 1.35/0.57    inference(avatar_component_clause,[],[f150])).
% 1.35/0.57  fof(f160,plain,(
% 1.35/0.57    spl6_11 | ~spl6_6 | ~spl6_10),
% 1.35/0.57    inference(avatar_split_clause,[],[f153,f150,f129,f157])).
% 1.35/0.57  fof(f153,plain,(
% 1.35/0.57    l1_pre_topc(sK1) | (~spl6_6 | ~spl6_10)),
% 1.35/0.57    inference(resolution,[],[f151,f131])).
% 1.35/0.57  fof(f152,plain,(
% 1.35/0.57    spl6_10 | ~spl6_3),
% 1.35/0.57    inference(avatar_split_clause,[],[f148,f114,f150])).
% 1.35/0.57  fof(f148,plain,(
% 1.35/0.57    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl6_3),
% 1.35/0.57    inference(resolution,[],[f71,f116])).
% 1.35/0.57  fof(f71,plain,(
% 1.35/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.35/0.57    inference(cnf_transformation,[],[f21])).
% 1.35/0.57  fof(f21,plain,(
% 1.35/0.57    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.35/0.57    inference(ennf_transformation,[],[f2])).
% 1.35/0.57  fof(f2,axiom,(
% 1.35/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.35/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.35/0.57  fof(f147,plain,(
% 1.35/0.57    spl6_9),
% 1.35/0.57    inference(avatar_split_clause,[],[f66,f144])).
% 1.35/0.57  fof(f66,plain,(
% 1.35/0.57    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.35/0.57    inference(cnf_transformation,[],[f47])).
% 1.35/0.57  fof(f142,plain,(
% 1.35/0.57    spl6_8),
% 1.35/0.57    inference(avatar_split_clause,[],[f65,f139])).
% 1.35/0.57  fof(f65,plain,(
% 1.35/0.57    r1_tsep_1(sK1,sK2)),
% 1.35/0.57    inference(cnf_transformation,[],[f47])).
% 1.35/0.57  fof(f137,plain,(
% 1.35/0.57    spl6_7),
% 1.35/0.57    inference(avatar_split_clause,[],[f64,f134])).
% 1.35/0.57  fof(f64,plain,(
% 1.35/0.57    m1_pre_topc(sK2,sK0)),
% 1.35/0.57    inference(cnf_transformation,[],[f47])).
% 1.35/0.57  fof(f132,plain,(
% 1.35/0.57    spl6_6),
% 1.35/0.57    inference(avatar_split_clause,[],[f62,f129])).
% 1.35/0.57  fof(f62,plain,(
% 1.35/0.57    m1_pre_topc(sK1,sK0)),
% 1.35/0.57    inference(cnf_transformation,[],[f47])).
% 1.35/0.57  fof(f127,plain,(
% 1.35/0.57    ~spl6_5),
% 1.35/0.57    inference(avatar_split_clause,[],[f63,f124])).
% 1.35/0.57  fof(f63,plain,(
% 1.35/0.57    ~v2_struct_0(sK2)),
% 1.35/0.57    inference(cnf_transformation,[],[f47])).
% 1.35/0.57  fof(f117,plain,(
% 1.35/0.57    spl6_3),
% 1.35/0.57    inference(avatar_split_clause,[],[f60,f114])).
% 1.35/0.57  fof(f60,plain,(
% 1.35/0.57    l1_pre_topc(sK0)),
% 1.35/0.57    inference(cnf_transformation,[],[f47])).
% 1.35/0.57  fof(f112,plain,(
% 1.35/0.57    spl6_2),
% 1.35/0.57    inference(avatar_split_clause,[],[f59,f109])).
% 1.35/0.57  fof(f59,plain,(
% 1.35/0.57    v2_pre_topc(sK0)),
% 1.35/0.57    inference(cnf_transformation,[],[f47])).
% 1.35/0.57  fof(f107,plain,(
% 1.35/0.57    ~spl6_1),
% 1.35/0.57    inference(avatar_split_clause,[],[f58,f104])).
% 1.35/0.57  fof(f58,plain,(
% 1.35/0.57    ~v2_struct_0(sK0)),
% 1.35/0.57    inference(cnf_transformation,[],[f47])).
% 1.35/0.57  % SZS output end Proof for theBenchmark
% 1.35/0.57  % (3455)------------------------------
% 1.35/0.57  % (3455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (3455)Termination reason: Refutation
% 1.35/0.57  
% 1.35/0.57  % (3455)Memory used [KB]: 7036
% 1.35/0.57  % (3455)Time elapsed: 0.120 s
% 1.35/0.57  % (3455)------------------------------
% 1.35/0.57  % (3455)------------------------------
% 1.35/0.57  % (3465)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.66/0.57  % (3452)Success in time 0.21 s
%------------------------------------------------------------------------------
