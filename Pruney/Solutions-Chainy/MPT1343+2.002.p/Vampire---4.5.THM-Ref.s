%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 279 expanded)
%              Number of leaves         :   38 ( 143 expanded)
%              Depth                    :    7
%              Number of atoms          :  433 (1302 expanded)
%              Number of equality atoms :   92 ( 322 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f69,f74,f79,f84,f89,f104,f105,f118,f123,f128,f133,f145,f151,f153,f159,f165,f174,f184,f212,f213,f215,f227,f240])).

fof(f240,plain,
    ( ~ spl4_21
    | ~ spl4_7
    | ~ spl4_2
    | spl4_30 ),
    inference(avatar_split_clause,[],[f235,f224,f51,f76,f162])).

fof(f162,plain,
    ( spl4_21
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f76,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f51,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f224,plain,
    ( spl4_30
  <=> k9_relat_1(sK2,sK3) = k10_relat_1(k2_funct_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f235,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_30 ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,
    ( k9_relat_1(sK2,sK3) != k9_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_30 ),
    inference(superposition,[],[f226,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f226,plain,
    ( k9_relat_1(sK2,sK3) != k10_relat_1(k2_funct_1(sK2),sK3)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f224])).

fof(f227,plain,
    ( ~ spl4_30
    | spl4_24
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f222,f204,f181,f224])).

fof(f181,plain,
    ( spl4_24
  <=> k9_relat_1(sK2,sK3) = k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f204,plain,
    ( spl4_27
  <=> k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f222,plain,
    ( k9_relat_1(sK2,sK3) != k10_relat_1(k2_funct_1(sK2),sK3)
    | spl4_24
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f183,f206])).

fof(f206,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f204])).

fof(f183,plain,
    ( k9_relat_1(sK2,sK3) != k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f215,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f213,plain,
    ( ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19
    | spl4_27
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f192,f107,f51,f204,f148,f142,f76])).

fof(f142,plain,
    ( spl4_18
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f148,plain,
    ( spl4_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f107,plain,
    ( spl4_12
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f192,plain,
    ( ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f37,f109])).

fof(f109,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f212,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f185,f148,f142,f107,f76,f51,f209])).

fof(f209,plain,
    ( spl4_28
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f185,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f78,f53,f144,f150,f109,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f150,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f148])).

fof(f144,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f53,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f78,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f184,plain,
    ( ~ spl4_23
    | ~ spl4_24
    | spl4_22 ),
    inference(avatar_split_clause,[],[f175,f171,f181,f177])).

fof(f177,plain,
    ( spl4_23
  <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f171,plain,
    ( spl4_22
  <=> k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) = k9_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f175,plain,
    ( k9_relat_1(sK2,sK3) != k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | spl4_22 ),
    inference(superposition,[],[f173,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f173,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k9_relat_1(sK2,sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f171])).

fof(f174,plain,
    ( ~ spl4_22
    | ~ spl4_19
    | spl4_20 ),
    inference(avatar_split_clause,[],[f169,f156,f148,f171])).

fof(f156,plain,
    ( spl4_20
  <=> k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f169,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k9_relat_1(sK2,sK3)
    | ~ spl4_19
    | spl4_20 ),
    inference(backward_demodulation,[],[f158,f168])).

fof(f168,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f150,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f158,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f156])).

fof(f165,plain,
    ( spl4_21
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f160,f148,f162])).

fof(f160,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f150,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f159,plain,
    ( ~ spl4_20
    | ~ spl4_10
    | spl4_13 ),
    inference(avatar_split_clause,[],[f154,f115,f95,f156])).

fof(f95,plain,
    ( spl4_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f115,plain,
    ( spl4_13
  <=> k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f154,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | ~ spl4_10
    | spl4_13 ),
    inference(forward_demodulation,[],[f117,f97])).

fof(f97,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f117,plain,
    ( k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f153,plain,
    ( spl4_12
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f152,f120,f95,f107])).

fof(f120,plain,
    ( spl4_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f152,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f122,f97])).

fof(f122,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f151,plain,
    ( spl4_19
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f146,f125,f95,f148])).

fof(f125,plain,
    ( spl4_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f127,f97])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f145,plain,
    ( spl4_18
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f140,f130,f95,f142])).

fof(f130,plain,
    ( spl4_16
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f140,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f132,f97])).

fof(f132,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f133,plain,
    ( spl4_16
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f113,f100,f71,f130])).

fof(f71,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f100,plain,
    ( spl4_11
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f113,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f73,f102])).

fof(f102,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f73,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f128,plain,
    ( spl4_15
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f112,f100,f66,f125])).

fof(f66,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f68,f102])).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f123,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f111,f100,f56,f120])).

fof(f56,plain,
    ( spl4_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f111,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f58,f102])).

fof(f58,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f118,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f110,f100,f46,f115])).

fof(f46,plain,
    ( spl4_1
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f110,plain,
    ( k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_1
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f48,f102])).

fof(f48,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f105,plain,
    ( spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f93,f86,f95])).

fof(f86,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f93,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f43,f88])).

fof(f88,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f104,plain,
    ( spl4_11
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f92,f81,f100])).

fof(f81,plain,
    ( spl4_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f92,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f43,f83])).

fof(f83,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f89,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f27,f86])).

fof(f27,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f25,f24,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
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

fof(f24,plain,
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

fof(f25,plain,
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f84,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f28,f81])).

fof(f28,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f76])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f33,f56])).

fof(f33,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f34,f51])).

fof(f34,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f46])).

fof(f35,plain,(
    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:52:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (19305)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.45  % (19305)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f241,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f49,f54,f59,f69,f74,f79,f84,f89,f104,f105,f118,f123,f128,f133,f145,f151,f153,f159,f165,f174,f184,f212,f213,f215,f227,f240])).
% 0.20/0.45  fof(f240,plain,(
% 0.20/0.45    ~spl4_21 | ~spl4_7 | ~spl4_2 | spl4_30),
% 0.20/0.45    inference(avatar_split_clause,[],[f235,f224,f51,f76,f162])).
% 0.20/0.45  fof(f162,plain,(
% 0.20/0.45    spl4_21 <=> v1_relat_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    spl4_7 <=> v1_funct_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    spl4_2 <=> v2_funct_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.45  fof(f224,plain,(
% 0.20/0.45    spl4_30 <=> k9_relat_1(sK2,sK3) = k10_relat_1(k2_funct_1(sK2),sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.45  fof(f235,plain,(
% 0.20/0.45    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_30),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f234])).
% 0.20/0.45  fof(f234,plain,(
% 0.20/0.45    k9_relat_1(sK2,sK3) != k9_relat_1(sK2,sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_30),
% 0.20/0.45    inference(superposition,[],[f226,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(flattening,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.20/0.45  fof(f226,plain,(
% 0.20/0.45    k9_relat_1(sK2,sK3) != k10_relat_1(k2_funct_1(sK2),sK3) | spl4_30),
% 0.20/0.45    inference(avatar_component_clause,[],[f224])).
% 0.20/0.45  fof(f227,plain,(
% 0.20/0.45    ~spl4_30 | spl4_24 | ~spl4_27),
% 0.20/0.45    inference(avatar_split_clause,[],[f222,f204,f181,f224])).
% 0.20/0.45  fof(f181,plain,(
% 0.20/0.45    spl4_24 <=> k9_relat_1(sK2,sK3) = k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.45  fof(f204,plain,(
% 0.20/0.45    spl4_27 <=> k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.45  fof(f222,plain,(
% 0.20/0.45    k9_relat_1(sK2,sK3) != k10_relat_1(k2_funct_1(sK2),sK3) | (spl4_24 | ~spl4_27)),
% 0.20/0.45    inference(forward_demodulation,[],[f183,f206])).
% 0.20/0.45  fof(f206,plain,(
% 0.20/0.45    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~spl4_27),
% 0.20/0.45    inference(avatar_component_clause,[],[f204])).
% 0.20/0.45  fof(f183,plain,(
% 0.20/0.45    k9_relat_1(sK2,sK3) != k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_24),
% 0.20/0.45    inference(avatar_component_clause,[],[f181])).
% 0.20/0.45  fof(f215,plain,(
% 0.20/0.45    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_funct_1(sK2) | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.45  fof(f213,plain,(
% 0.20/0.45    ~spl4_7 | ~spl4_18 | ~spl4_19 | spl4_27 | ~spl4_2 | ~spl4_12),
% 0.20/0.45    inference(avatar_split_clause,[],[f192,f107,f51,f204,f148,f142,f76])).
% 0.20/0.45  fof(f142,plain,(
% 0.20/0.45    spl4_18 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.45  fof(f148,plain,(
% 0.20/0.45    spl4_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.45  fof(f107,plain,(
% 0.20/0.45    spl4_12 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.45  fof(f192,plain,(
% 0.20/0.45    ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl4_12),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f189])).
% 0.20/0.45  fof(f189,plain,(
% 0.20/0.45    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl4_12),
% 0.20/0.45    inference(superposition,[],[f37,f109])).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_12),
% 0.20/0.45    inference(avatar_component_clause,[],[f107])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.45  fof(f212,plain,(
% 0.20/0.45    spl4_28 | ~spl4_2 | ~spl4_7 | ~spl4_12 | ~spl4_18 | ~spl4_19),
% 0.20/0.45    inference(avatar_split_clause,[],[f185,f148,f142,f107,f76,f51,f209])).
% 0.20/0.45  fof(f209,plain,(
% 0.20/0.45    spl4_28 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.45  fof(f185,plain,(
% 0.20/0.45    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl4_2 | ~spl4_7 | ~spl4_12 | ~spl4_18 | ~spl4_19)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f78,f53,f144,f150,f109,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.45    inference(flattening,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.45  fof(f150,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_19),
% 0.20/0.45    inference(avatar_component_clause,[],[f148])).
% 0.20/0.45  fof(f144,plain,(
% 0.20/0.45    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_18),
% 0.20/0.45    inference(avatar_component_clause,[],[f142])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    v2_funct_1(sK2) | ~spl4_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f51])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    v1_funct_1(sK2) | ~spl4_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f76])).
% 0.20/0.45  fof(f184,plain,(
% 0.20/0.45    ~spl4_23 | ~spl4_24 | spl4_22),
% 0.20/0.45    inference(avatar_split_clause,[],[f175,f171,f181,f177])).
% 0.20/0.45  fof(f177,plain,(
% 0.20/0.45    spl4_23 <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.45  fof(f171,plain,(
% 0.20/0.45    spl4_22 <=> k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) = k9_relat_1(sK2,sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.45  fof(f175,plain,(
% 0.20/0.45    k9_relat_1(sK2,sK3) != k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | spl4_22),
% 0.20/0.45    inference(superposition,[],[f173,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.45  fof(f173,plain,(
% 0.20/0.45    k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k9_relat_1(sK2,sK3) | spl4_22),
% 0.20/0.45    inference(avatar_component_clause,[],[f171])).
% 0.20/0.45  fof(f174,plain,(
% 0.20/0.45    ~spl4_22 | ~spl4_19 | spl4_20),
% 0.20/0.45    inference(avatar_split_clause,[],[f169,f156,f148,f171])).
% 0.20/0.45  fof(f156,plain,(
% 0.20/0.45    spl4_20 <=> k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.45  fof(f169,plain,(
% 0.20/0.45    k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k9_relat_1(sK2,sK3) | (~spl4_19 | spl4_20)),
% 0.20/0.45    inference(backward_demodulation,[],[f158,f168])).
% 0.20/0.45  fof(f168,plain,(
% 0.20/0.45    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | ~spl4_19),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f150,f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.45  fof(f158,plain,(
% 0.20/0.45    k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_20),
% 0.20/0.45    inference(avatar_component_clause,[],[f156])).
% 0.20/0.45  fof(f165,plain,(
% 0.20/0.45    spl4_21 | ~spl4_19),
% 0.20/0.45    inference(avatar_split_clause,[],[f160,f148,f162])).
% 0.20/0.45  fof(f160,plain,(
% 0.20/0.45    v1_relat_1(sK2) | ~spl4_19),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f150,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.45  fof(f159,plain,(
% 0.20/0.45    ~spl4_20 | ~spl4_10 | spl4_13),
% 0.20/0.45    inference(avatar_split_clause,[],[f154,f115,f95,f156])).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    spl4_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    spl4_13 <=> k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.45  fof(f154,plain,(
% 0.20/0.45    k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (~spl4_10 | spl4_13)),
% 0.20/0.45    inference(forward_demodulation,[],[f117,f97])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f95])).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_13),
% 0.20/0.45    inference(avatar_component_clause,[],[f115])).
% 0.20/0.45  fof(f153,plain,(
% 0.20/0.45    spl4_12 | ~spl4_10 | ~spl4_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f152,f120,f95,f107])).
% 0.20/0.45  fof(f120,plain,(
% 0.20/0.45    spl4_14 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.45  fof(f152,plain,(
% 0.20/0.45    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_10 | ~spl4_14)),
% 0.20/0.45    inference(forward_demodulation,[],[f122,f97])).
% 0.20/0.45  fof(f122,plain,(
% 0.20/0.45    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_14),
% 0.20/0.45    inference(avatar_component_clause,[],[f120])).
% 0.20/0.45  fof(f151,plain,(
% 0.20/0.45    spl4_19 | ~spl4_10 | ~spl4_15),
% 0.20/0.45    inference(avatar_split_clause,[],[f146,f125,f95,f148])).
% 0.20/0.45  fof(f125,plain,(
% 0.20/0.45    spl4_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.45  fof(f146,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_10 | ~spl4_15)),
% 0.20/0.45    inference(forward_demodulation,[],[f127,f97])).
% 0.20/0.45  fof(f127,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_15),
% 0.20/0.45    inference(avatar_component_clause,[],[f125])).
% 0.20/0.45  fof(f145,plain,(
% 0.20/0.45    spl4_18 | ~spl4_10 | ~spl4_16),
% 0.20/0.45    inference(avatar_split_clause,[],[f140,f130,f95,f142])).
% 0.20/0.45  fof(f130,plain,(
% 0.20/0.45    spl4_16 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.45  fof(f140,plain,(
% 0.20/0.45    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_10 | ~spl4_16)),
% 0.20/0.45    inference(forward_demodulation,[],[f132,f97])).
% 0.20/0.45  fof(f132,plain,(
% 0.20/0.45    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f130])).
% 0.20/0.45  fof(f133,plain,(
% 0.20/0.45    spl4_16 | ~spl4_6 | ~spl4_11),
% 0.20/0.45    inference(avatar_split_clause,[],[f113,f100,f71,f130])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    spl4_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    spl4_11 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_6 | ~spl4_11)),
% 0.20/0.45    inference(backward_demodulation,[],[f73,f102])).
% 0.20/0.45  fof(f102,plain,(
% 0.20/0.45    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_11),
% 0.20/0.45    inference(avatar_component_clause,[],[f100])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_6),
% 0.20/0.45    inference(avatar_component_clause,[],[f71])).
% 0.20/0.45  fof(f128,plain,(
% 0.20/0.45    spl4_15 | ~spl4_5 | ~spl4_11),
% 0.20/0.45    inference(avatar_split_clause,[],[f112,f100,f66,f125])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_5 | ~spl4_11)),
% 0.20/0.45    inference(backward_demodulation,[],[f68,f102])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f66])).
% 0.20/0.45  fof(f123,plain,(
% 0.20/0.45    spl4_14 | ~spl4_3 | ~spl4_11),
% 0.20/0.45    inference(avatar_split_clause,[],[f111,f100,f56,f120])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    spl4_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.45  fof(f111,plain,(
% 0.20/0.45    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_3 | ~spl4_11)),
% 0.20/0.45    inference(backward_demodulation,[],[f58,f102])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl4_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f56])).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    ~spl4_13 | spl4_1 | ~spl4_11),
% 0.20/0.45    inference(avatar_split_clause,[],[f110,f100,f46,f115])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    spl4_1 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (spl4_1 | ~spl4_11)),
% 0.20/0.45    inference(backward_demodulation,[],[f48,f102])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | spl4_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f46])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    spl4_10 | ~spl4_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f93,f86,f95])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    spl4_9 <=> l1_struct_0(sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_9),
% 0.20/0.45    inference(resolution,[],[f43,f88])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    l1_struct_0(sK0) | ~spl4_9),
% 0.20/0.45    inference(avatar_component_clause,[],[f86])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    spl4_11 | ~spl4_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f92,f81,f100])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    spl4_8 <=> l1_struct_0(sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_8),
% 0.20/0.45    inference(resolution,[],[f43,f83])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    l1_struct_0(sK1) | ~spl4_8),
% 0.20/0.45    inference(avatar_component_clause,[],[f81])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    spl4_9),
% 0.20/0.45    inference(avatar_split_clause,[],[f27,f86])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    l1_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    (((k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f25,f24,f23,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.20/0.45    inference(negated_conjecture,[],[f8])).
% 0.20/0.45  fof(f8,conjecture,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    spl4_8),
% 0.20/0.45    inference(avatar_split_clause,[],[f28,f81])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    l1_struct_0(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    spl4_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f29,f76])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    v1_funct_1(sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    spl4_6),
% 0.20/0.45    inference(avatar_split_clause,[],[f30,f71])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    spl4_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f31,f66])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    spl4_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f33,f56])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    spl4_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f34,f51])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    v2_funct_1(sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ~spl4_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f35,f46])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (19305)------------------------------
% 0.20/0.45  % (19305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (19305)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (19305)Memory used [KB]: 10746
% 0.20/0.45  % (19305)Time elapsed: 0.016 s
% 0.20/0.45  % (19305)------------------------------
% 0.20/0.45  % (19305)------------------------------
% 0.20/0.46  % (19293)Success in time 0.099 s
%------------------------------------------------------------------------------
