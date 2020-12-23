%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 272 expanded)
%              Number of leaves         :   36 ( 138 expanded)
%              Depth                    :    7
%              Number of atoms          :  414 (1275 expanded)
%              Number of equality atoms :   87 ( 314 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f69,f74,f79,f84,f89,f104,f105,f119,f124,f134,f139,f145,f151,f153,f159,f165,f174,f184,f198,f207,f222,f249])).

fof(f249,plain,
    ( ~ spl4_21
    | ~ spl4_7
    | ~ spl4_2
    | spl4_29 ),
    inference(avatar_split_clause,[],[f244,f219,f51,f76,f162])).

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

fof(f219,plain,
    ( spl4_29
  <=> k10_relat_1(sK2,sK3) = k9_relat_1(k2_funct_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f244,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_29 ),
    inference(trivial_inequality_removal,[],[f243])).

fof(f243,plain,
    ( k10_relat_1(sK2,sK3) != k10_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_29 ),
    inference(superposition,[],[f221,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f221,plain,
    ( k10_relat_1(sK2,sK3) != k9_relat_1(k2_funct_1(sK2),sK3)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f219])).

fof(f222,plain,
    ( ~ spl4_29
    | spl4_24
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f209,f203,f181,f219])).

fof(f181,plain,
    ( spl4_24
  <=> k10_relat_1(sK2,sK3) = k9_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f203,plain,
    ( spl4_27
  <=> k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f209,plain,
    ( k10_relat_1(sK2,sK3) != k9_relat_1(k2_funct_1(sK2),sK3)
    | spl4_24
    | ~ spl4_27 ),
    inference(backward_demodulation,[],[f183,f205])).

fof(f205,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f203])).

fof(f183,plain,
    ( k10_relat_1(sK2,sK3) != k9_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f207,plain,
    ( ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19
    | spl4_27
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f201,f107,f51,f203,f148,f142,f76])).

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

fof(f201,plain,
    ( ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,
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
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f198,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f197,f148,f142,f76,f177])).

fof(f177,plain,
    ( spl4_23
  <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f197,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f78,f144,f150,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f150,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f148])).

fof(f144,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f78,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f184,plain,
    ( ~ spl4_23
    | ~ spl4_24
    | spl4_22 ),
    inference(avatar_split_clause,[],[f175,f171,f181,f177])).

fof(f171,plain,
    ( spl4_22
  <=> k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) = k10_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f175,plain,
    ( k10_relat_1(sK2,sK3) != k9_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | spl4_22 ),
    inference(superposition,[],[f173,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f173,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k10_relat_1(sK2,sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f171])).

fof(f174,plain,
    ( ~ spl4_22
    | ~ spl4_19
    | spl4_20 ),
    inference(avatar_split_clause,[],[f169,f156,f148,f171])).

fof(f156,plain,
    ( spl4_20
  <=> k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f169,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k10_relat_1(sK2,sK3)
    | ~ spl4_19
    | spl4_20 ),
    inference(backward_demodulation,[],[f158,f168])).

fof(f168,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f150,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f158,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
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

% (20223)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f159,plain,
    ( ~ spl4_20
    | ~ spl4_10
    | spl4_13 ),
    inference(avatar_split_clause,[],[f154,f116,f95,f156])).

fof(f95,plain,
    ( spl4_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f116,plain,
    ( spl4_13
  <=> k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f154,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | ~ spl4_10
    | spl4_13 ),
    inference(forward_demodulation,[],[f118,f97])).

fof(f97,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f118,plain,
    ( k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f153,plain,
    ( spl4_12
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f152,f121,f95,f107])).

fof(f121,plain,
    ( spl4_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f152,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f123,f97])).

fof(f123,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f151,plain,
    ( spl4_19
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f146,f131,f95,f148])).

fof(f131,plain,
    ( spl4_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f133,f97])).

fof(f133,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f145,plain,
    ( spl4_18
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f140,f136,f95,f142])).

fof(f136,plain,
    ( spl4_17
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f140,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_10
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f138,f97])).

fof(f138,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( spl4_17
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f114,f100,f71,f136])).

fof(f71,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f100,plain,
    ( spl4_11
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f114,plain,
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

fof(f134,plain,
    ( spl4_16
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f113,f100,f66,f131])).

fof(f66,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f113,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f68,f102])).

% (20206)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f124,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f111,f100,f56,f121])).

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

fof(f119,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f110,f100,f46,f116])).

fof(f46,plain,
    ( spl4_1
  <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f110,plain,
    ( k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_1
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f48,f102])).

fof(f48,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

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
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
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
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
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
                ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
          & v2_funct_1(sK2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
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
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
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
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_funct_1(X2)
                        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                     => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
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
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).

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
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (20207)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.48  % (20207)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f250,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f49,f54,f59,f69,f74,f79,f84,f89,f104,f105,f119,f124,f134,f139,f145,f151,f153,f159,f165,f174,f184,f198,f207,f222,f249])).
% 0.22/0.48  fof(f249,plain,(
% 0.22/0.48    ~spl4_21 | ~spl4_7 | ~spl4_2 | spl4_29),
% 0.22/0.48    inference(avatar_split_clause,[],[f244,f219,f51,f76,f162])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    spl4_21 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl4_7 <=> v1_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl4_2 <=> v2_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f219,plain,(
% 0.22/0.48    spl4_29 <=> k10_relat_1(sK2,sK3) = k9_relat_1(k2_funct_1(sK2),sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.48  fof(f244,plain,(
% 0.22/0.48    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_29),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f243])).
% 0.22/0.48  fof(f243,plain,(
% 0.22/0.48    k10_relat_1(sK2,sK3) != k10_relat_1(sK2,sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_29),
% 0.22/0.48    inference(superposition,[],[f221,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.22/0.48  fof(f221,plain,(
% 0.22/0.48    k10_relat_1(sK2,sK3) != k9_relat_1(k2_funct_1(sK2),sK3) | spl4_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f219])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    ~spl4_29 | spl4_24 | ~spl4_27),
% 0.22/0.48    inference(avatar_split_clause,[],[f209,f203,f181,f219])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    spl4_24 <=> k10_relat_1(sK2,sK3) = k9_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    spl4_27 <=> k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.48  fof(f209,plain,(
% 0.22/0.48    k10_relat_1(sK2,sK3) != k9_relat_1(k2_funct_1(sK2),sK3) | (spl4_24 | ~spl4_27)),
% 0.22/0.48    inference(backward_demodulation,[],[f183,f205])).
% 0.22/0.48  fof(f205,plain,(
% 0.22/0.48    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~spl4_27),
% 0.22/0.48    inference(avatar_component_clause,[],[f203])).
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    k10_relat_1(sK2,sK3) != k9_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f181])).
% 0.22/0.48  fof(f207,plain,(
% 0.22/0.48    ~spl4_7 | ~spl4_18 | ~spl4_19 | spl4_27 | ~spl4_2 | ~spl4_12),
% 0.22/0.48    inference(avatar_split_clause,[],[f201,f107,f51,f203,f148,f142,f76])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    spl4_18 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    spl4_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    spl4_12 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl4_12),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f200])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl4_12),
% 0.22/0.48    inference(superposition,[],[f37,f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f107])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    spl4_23 | ~spl4_7 | ~spl4_18 | ~spl4_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f197,f148,f142,f76,f177])).
% 0.22/0.48  fof(f177,plain,(
% 0.22/0.48    spl4_23 <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl4_7 | ~spl4_18 | ~spl4_19)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f78,f144,f150,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f148])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_18),
% 0.22/0.48    inference(avatar_component_clause,[],[f142])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    v1_funct_1(sK2) | ~spl4_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f76])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    ~spl4_23 | ~spl4_24 | spl4_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f175,f171,f181,f177])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    spl4_22 <=> k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) = k10_relat_1(sK2,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    k10_relat_1(sK2,sK3) != k9_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | spl4_22),
% 0.22/0.48    inference(superposition,[],[f173,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k10_relat_1(sK2,sK3) | spl4_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f171])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    ~spl4_22 | ~spl4_19 | spl4_20),
% 0.22/0.48    inference(avatar_split_clause,[],[f169,f156,f148,f171])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    spl4_20 <=> k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k10_relat_1(sK2,sK3) | (~spl4_19 | spl4_20)),
% 0.22/0.48    inference(backward_demodulation,[],[f158,f168])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | ~spl4_19),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f150,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f156])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    spl4_21 | ~spl4_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f160,f148,f162])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl4_19),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f150,f44])).
% 0.22/0.48  % (20223)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ~spl4_20 | ~spl4_10 | spl4_13),
% 0.22/0.48    inference(avatar_split_clause,[],[f154,f116,f95,f156])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl4_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl4_13 <=> k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (~spl4_10 | spl4_13)),
% 0.22/0.48    inference(forward_demodulation,[],[f118,f97])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f95])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f116])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    spl4_12 | ~spl4_10 | ~spl4_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f152,f121,f95,f107])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    spl4_14 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_10 | ~spl4_14)),
% 0.22/0.48    inference(forward_demodulation,[],[f123,f97])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f121])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    spl4_19 | ~spl4_10 | ~spl4_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f146,f131,f95,f148])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl4_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_10 | ~spl4_16)),
% 0.22/0.48    inference(forward_demodulation,[],[f133,f97])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f131])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl4_18 | ~spl4_10 | ~spl4_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f140,f136,f95,f142])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl4_17 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_10 | ~spl4_17)),
% 0.22/0.48    inference(forward_demodulation,[],[f138,f97])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f136])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    spl4_17 | ~spl4_6 | ~spl4_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f114,f100,f71,f136])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl4_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    spl4_11 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_6 | ~spl4_11)),
% 0.22/0.48    inference(backward_demodulation,[],[f73,f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f100])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    spl4_16 | ~spl4_5 | ~spl4_11),
% 0.22/0.48    inference(avatar_split_clause,[],[f113,f100,f66,f131])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_5 | ~spl4_11)),
% 0.22/0.48    inference(backward_demodulation,[],[f68,f102])).
% 0.22/0.49  % (20206)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    spl4_14 | ~spl4_3 | ~spl4_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f111,f100,f56,f121])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl4_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_3 | ~spl4_11)),
% 0.22/0.49    inference(backward_demodulation,[],[f58,f102])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl4_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ~spl4_13 | spl4_1 | ~spl4_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f110,f100,f46,f116])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl4_1 <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (spl4_1 | ~spl4_11)),
% 0.22/0.49    inference(backward_demodulation,[],[f48,f102])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f46])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl4_10 | ~spl4_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f93,f86,f95])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl4_9 <=> l1_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_9),
% 0.22/0.49    inference(resolution,[],[f43,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    l1_struct_0(sK0) | ~spl4_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f86])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl4_11 | ~spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f92,f81,f100])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl4_8 <=> l1_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_8),
% 0.22/0.49    inference(resolution,[],[f43,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    l1_struct_0(sK1) | ~spl4_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f81])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl4_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f86])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    l1_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    (((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f25,f24,f23,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f81])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    l1_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl4_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f76])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl4_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f71])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f66])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl4_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f56])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f51])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v2_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ~spl4_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f46])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (20207)------------------------------
% 0.22/0.49  % (20207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (20207)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (20207)Memory used [KB]: 10874
% 0.22/0.49  % (20207)Time elapsed: 0.070 s
% 0.22/0.49  % (20207)------------------------------
% 0.22/0.49  % (20207)------------------------------
% 0.22/0.50  % (20200)Success in time 0.133 s
%------------------------------------------------------------------------------
