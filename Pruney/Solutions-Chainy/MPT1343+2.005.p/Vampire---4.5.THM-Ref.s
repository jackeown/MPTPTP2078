%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 265 expanded)
%              Number of leaves         :   35 ( 129 expanded)
%              Depth                    :    8
%              Number of atoms          :  443 (1294 expanded)
%              Number of equality atoms :  101 ( 320 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f71,f76,f81,f86,f91,f104,f115,f121,f157,f164,f165,f180,f189,f215,f279,f287,f305,f323,f352])).

fof(f352,plain,
    ( ~ spl4_13
    | spl4_22
    | ~ spl4_33
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f351])).

fof(f351,plain,
    ( $false
    | ~ spl4_13
    | spl4_22
    | ~ spl4_33
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f350,f322])).

fof(f322,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl4_37
  <=> ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f350,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k9_relat_1(sK2,sK3)
    | ~ spl4_13
    | spl4_22
    | ~ spl4_33
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f349,f304])).

fof(f304,plain,
    ( ! [X1] : k9_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl4_35
  <=> ! [X1] : k9_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f349,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3)
    | ~ spl4_13
    | spl4_22
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f348,f286])).

fof(f286,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl4_33
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f348,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | ~ spl4_13
    | spl4_22 ),
    inference(forward_demodulation,[],[f214,f120])).

fof(f120,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_13
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f214,plain,
    ( k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl4_22
  <=> k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f323,plain,
    ( spl4_37
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f319,f178,f118,f112,f321])).

fof(f112,plain,
    ( spl4_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f178,plain,
    ( spl4_20
  <=> ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f319,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f318,f120])).

fof(f318,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f179,f114])).

fof(f114,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f179,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f178])).

fof(f305,plain,
    ( spl4_35
    | ~ spl4_11
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f301,f276,f102,f303])).

fof(f102,plain,
    ( spl4_11
  <=> ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f276,plain,
    ( spl4_32
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f301,plain,
    ( ! [X1] : k9_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)
    | ~ spl4_11
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f295,f103])).

fof(f103,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f295,plain,
    ( ! [X1] : k10_relat_1(k2_funct_1(sK2),X1) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)
    | ~ spl4_32 ),
    inference(resolution,[],[f278,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f278,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f276])).

fof(f287,plain,
    ( spl4_33
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f282,f161,f118,f112,f284])).

fof(f161,plain,
    ( spl4_19
  <=> k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f282,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f281,f120])).

fof(f281,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f163,f114])).

fof(f163,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f279,plain,
    ( spl4_32
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f274,f154,f118,f112,f276])).

fof(f154,plain,
    ( spl4_18
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f274,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f273,f114])).

fof(f273,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f156,f120])).

fof(f156,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f215,plain,
    ( ~ spl4_22
    | spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f207,f112,f48,f212])).

fof(f48,plain,
    ( spl4_1
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f207,plain,
    ( k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_1
    | ~ spl4_12 ),
    inference(superposition,[],[f50,f114])).

fof(f50,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f189,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f188,f68,f98])).

fof(f98,plain,
    ( spl4_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f68,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f188,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f174,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f174,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f180,plain,
    ( spl4_20
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f171,f68,f178])).

fof(f171,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
    | ~ spl4_5 ),
    inference(resolution,[],[f70,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f165,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f164,plain,
    ( ~ spl4_5
    | ~ spl4_16
    | spl4_19
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f159,f78,f73,f53,f161,f143,f68])).

fof(f143,plain,
    ( spl4_16
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f53,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f73,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f78,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f159,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f158,f80])).

fof(f80,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f158,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f137,f55])).

fof(f55,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f137,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f75,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f75,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f157,plain,
    ( ~ spl4_5
    | ~ spl4_16
    | spl4_18
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f152,f78,f73,f53,f154,f143,f68])).

fof(f152,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f151,f80])).

fof(f151,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f136,f55])).

fof(f136,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f121,plain,
    ( spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f116,f88,f118])).

fof(f88,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f116,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f90,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f90,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f115,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f110,f83,f112])).

fof(f83,plain,
    ( spl4_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f110,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f85,f40])).

fof(f85,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f104,plain,
    ( ~ spl4_10
    | ~ spl4_7
    | spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f92,f53,f102,f78,f98])).

fof(f92,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f91,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f28,f88])).

fof(f28,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
          & v2_funct_1(sK2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( v2_funct_1(X2)
                        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                     => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).

fof(f86,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f29,f83])).

fof(f29,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f58,plain,
    ( spl4_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f34,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f35,f53])).

fof(f35,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f36,f48])).

fof(f36,plain,(
    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:09:41 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.49  % (19406)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.49  % (19398)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (19398)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f353,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f51,f56,f61,f71,f76,f81,f86,f91,f104,f115,f121,f157,f164,f165,f180,f189,f215,f279,f287,f305,f323,f352])).
% 0.22/0.50  fof(f352,plain,(
% 0.22/0.50    ~spl4_13 | spl4_22 | ~spl4_33 | ~spl4_35 | ~spl4_37),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f351])).
% 0.22/0.50  fof(f351,plain,(
% 0.22/0.50    $false | (~spl4_13 | spl4_22 | ~spl4_33 | ~spl4_35 | ~spl4_37)),
% 0.22/0.50    inference(subsumption_resolution,[],[f350,f322])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | ~spl4_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f321])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    spl4_37 <=> ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.50  fof(f350,plain,(
% 0.22/0.50    k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k9_relat_1(sK2,sK3) | (~spl4_13 | spl4_22 | ~spl4_33 | ~spl4_35)),
% 0.22/0.50    inference(forward_demodulation,[],[f349,f304])).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    ( ! [X1] : (k9_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)) ) | ~spl4_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f303])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    spl4_35 <=> ! [X1] : k9_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.50  fof(f349,plain,(
% 0.22/0.50    k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) | (~spl4_13 | spl4_22 | ~spl4_33)),
% 0.22/0.50    inference(forward_demodulation,[],[f348,f286])).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f284])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    spl4_33 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.50  fof(f348,plain,(
% 0.22/0.50    k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (~spl4_13 | spl4_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f214,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl4_13 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f212])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    spl4_22 <=> k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    spl4_37 | ~spl4_12 | ~spl4_13 | ~spl4_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f319,f178,f118,f112,f321])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl4_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    spl4_20 <=> ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.50  fof(f319,plain,(
% 0.22/0.50    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | (~spl4_12 | ~spl4_13 | ~spl4_20)),
% 0.22/0.50    inference(forward_demodulation,[],[f318,f120])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | (~spl4_12 | ~spl4_20)),
% 0.22/0.50    inference(forward_demodulation,[],[f179,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f112])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | ~spl4_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f178])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    spl4_35 | ~spl4_11 | ~spl4_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f301,f276,f102,f303])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl4_11 <=> ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    spl4_32 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    ( ! [X1] : (k9_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)) ) | (~spl4_11 | ~spl4_32)),
% 0.22/0.50    inference(forward_demodulation,[],[f295,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)) ) | ~spl4_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f102])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    ( ! [X1] : (k10_relat_1(k2_funct_1(sK2),X1) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)) ) | ~spl4_32),
% 0.22/0.50    inference(resolution,[],[f278,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.50  fof(f278,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl4_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f276])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    spl4_33 | ~spl4_12 | ~spl4_13 | ~spl4_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f282,f161,f118,f112,f284])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl4_19 <=> k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_12 | ~spl4_13 | ~spl4_19)),
% 0.22/0.50    inference(forward_demodulation,[],[f281,f120])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_12 | ~spl4_19)),
% 0.22/0.50    inference(forward_demodulation,[],[f163,f114])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~spl4_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    spl4_32 | ~spl4_12 | ~spl4_13 | ~spl4_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f274,f154,f118,f112,f276])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    spl4_18 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl4_12 | ~spl4_13 | ~spl4_18)),
% 0.22/0.50    inference(forward_demodulation,[],[f273,f114])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0)))) | (~spl4_13 | ~spl4_18)),
% 0.22/0.50    inference(forward_demodulation,[],[f156,f120])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl4_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f154])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    ~spl4_22 | spl4_1 | ~spl4_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f207,f112,f48,f212])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl4_1 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (spl4_1 | ~spl4_12)),
% 0.22/0.50    inference(superposition,[],[f50,f114])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | spl4_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f48])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    spl4_10 | ~spl4_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f188,f68,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl4_10 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~spl4_5),
% 0.22/0.50    inference(subsumption_resolution,[],[f174,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl4_5),
% 0.22/0.50    inference(resolution,[],[f70,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    spl4_20 | ~spl4_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f171,f68,f178])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | ~spl4_5),
% 0.22/0.50    inference(resolution,[],[f70,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ~spl4_5 | ~spl4_16 | spl4_19 | ~spl4_2 | ~spl4_6 | ~spl4_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f159,f78,f73,f53,f161,f143,f68])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    spl4_16 <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl4_2 <=> v2_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl4_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl4_7 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl4_2 | ~spl4_6 | ~spl4_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f158,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    v1_funct_1(sK2) | ~spl4_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | (~spl4_2 | ~spl4_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f137,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~spl4_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~spl4_6),
% 0.22/0.50    inference(resolution,[],[f75,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ~spl4_5 | ~spl4_16 | spl4_18 | ~spl4_2 | ~spl4_6 | ~spl4_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f152,f78,f73,f53,f154,f143,f68])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl4_2 | ~spl4_6 | ~spl4_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f151,f80])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | (~spl4_2 | ~spl4_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f136,f55])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~spl4_6),
% 0.22/0.50    inference(resolution,[],[f75,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl4_13 | ~spl4_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f116,f88,f118])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl4_9 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_9),
% 0.22/0.50    inference(resolution,[],[f90,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl4_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    spl4_12 | ~spl4_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f110,f83,f112])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl4_8 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_8),
% 0.22/0.50    inference(resolution,[],[f85,f40])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl4_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f83])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ~spl4_10 | ~spl4_7 | spl4_11 | ~spl4_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f92,f53,f102,f78,f98])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X0] : (k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_2),
% 0.22/0.50    inference(resolution,[],[f55,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl4_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f88])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    (((k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f26,f25,f24,f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    spl4_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f29,f83])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    l1_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    spl4_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f78])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    spl4_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f31,f73])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    spl4_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f32,f68])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f34,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    spl4_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f35,f53])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    v2_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ~spl4_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f36,f48])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (19398)------------------------------
% 0.22/0.51  % (19398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19398)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (19398)Memory used [KB]: 6396
% 0.22/0.51  % (19398)Time elapsed: 0.042 s
% 0.22/0.51  % (19398)------------------------------
% 0.22/0.51  % (19398)------------------------------
% 0.22/0.51  % (19397)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (19390)Success in time 0.138 s
%------------------------------------------------------------------------------
