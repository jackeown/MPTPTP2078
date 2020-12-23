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
% DateTime   : Thu Dec  3 13:14:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 274 expanded)
%              Number of leaves         :   37 ( 139 expanded)
%              Depth                    :    7
%              Number of atoms          :  419 (1280 expanded)
%              Number of equality atoms :   87 ( 314 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f71,f76,f81,f86,f91,f106,f107,f120,f125,f130,f135,f147,f153,f155,f161,f167,f175,f186,f200,f209,f224,f251])).

fof(f251,plain,
    ( ~ spl4_21
    | ~ spl4_7
    | ~ spl4_2
    | spl4_29 ),
    inference(avatar_split_clause,[],[f246,f221,f53,f78,f164])).

fof(f164,plain,
    ( spl4_21
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f78,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f53,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f221,plain,
    ( spl4_29
  <=> k9_relat_1(sK2,sK3) = k10_relat_1(k2_funct_1(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f246,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_29 ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,
    ( k9_relat_1(sK2,sK3) != k9_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_29 ),
    inference(superposition,[],[f223,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f223,plain,
    ( k9_relat_1(sK2,sK3) != k10_relat_1(k2_funct_1(sK2),sK3)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f221])).

fof(f224,plain,
    ( ~ spl4_29
    | spl4_24
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f211,f205,f183,f221])).

fof(f183,plain,
    ( spl4_24
  <=> k9_relat_1(sK2,sK3) = k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f205,plain,
    ( spl4_27
  <=> k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f211,plain,
    ( k9_relat_1(sK2,sK3) != k10_relat_1(k2_funct_1(sK2),sK3)
    | spl4_24
    | ~ spl4_27 ),
    inference(backward_demodulation,[],[f185,f207])).

fof(f207,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f205])).

fof(f185,plain,
    ( k9_relat_1(sK2,sK3) != k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f183])).

fof(f209,plain,
    ( ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19
    | spl4_27
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f203,f109,f53,f205,f150,f144,f78])).

fof(f144,plain,
    ( spl4_18
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f150,plain,
    ( spl4_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f109,plain,
    ( spl4_12
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f203,plain,
    ( ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f202])).

fof(f202,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f38,f111])).

fof(f111,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
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
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f200,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f199,f150,f144,f78,f179])).

fof(f179,plain,
    ( spl4_23
  <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f199,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f80,f146,f152,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f152,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f150])).

fof(f146,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f144])).

fof(f80,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f186,plain,
    ( ~ spl4_23
    | ~ spl4_24
    | spl4_22 ),
    inference(avatar_split_clause,[],[f177,f172,f183,f179])).

fof(f172,plain,
    ( spl4_22
  <=> k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) = k9_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f177,plain,
    ( k9_relat_1(sK2,sK3) != k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | spl4_22 ),
    inference(superposition,[],[f174,f37])).

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

fof(f174,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k9_relat_1(sK2,sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f172])).

fof(f175,plain,
    ( ~ spl4_22
    | ~ spl4_19
    | spl4_20 ),
    inference(avatar_split_clause,[],[f170,f158,f150,f172])).

fof(f158,plain,
    ( spl4_20
  <=> k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f170,plain,
    ( k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k9_relat_1(sK2,sK3)
    | ~ spl4_19
    | spl4_20 ),
    inference(backward_demodulation,[],[f160,f169])).

fof(f169,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f152,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f160,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f158])).

fof(f167,plain,
    ( spl4_21
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f162,f150,f164])).

fof(f162,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f46,f152,f45])).

fof(f45,plain,(
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

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f161,plain,
    ( ~ spl4_20
    | ~ spl4_10
    | spl4_13 ),
    inference(avatar_split_clause,[],[f156,f117,f97,f158])).

fof(f97,plain,
    ( spl4_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f117,plain,
    ( spl4_13
  <=> k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f156,plain,
    ( k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | ~ spl4_10
    | spl4_13 ),
    inference(forward_demodulation,[],[f119,f99])).

fof(f99,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f119,plain,
    ( k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f155,plain,
    ( spl4_12
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f154,f122,f97,f109])).

fof(f122,plain,
    ( spl4_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f154,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f124,f99])).

fof(f124,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f153,plain,
    ( spl4_19
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f148,f127,f97,f150])).

fof(f127,plain,
    ( spl4_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f129,f99])).

fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f147,plain,
    ( spl4_18
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f142,f132,f97,f144])).

fof(f132,plain,
    ( spl4_16
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f142,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f134,f99])).

fof(f134,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f135,plain,
    ( spl4_16
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f115,f102,f73,f132])).

fof(f73,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f102,plain,
    ( spl4_11
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f115,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f75,f104])).

fof(f104,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f75,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f130,plain,
    ( spl4_15
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f114,f102,f68,f127])).

fof(f68,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f70,f104])).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f125,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f113,f102,f58,f122])).

fof(f58,plain,
    ( spl4_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f113,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f60,f104])).

fof(f60,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f120,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f112,f102,f48,f117])).

fof(f48,plain,
    ( spl4_1
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f112,plain,
    ( k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_1
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f50,f104])).

fof(f50,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f107,plain,
    ( spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f95,f88,f97])).

fof(f88,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f95,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f44,f90])).

fof(f90,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f106,plain,
    ( spl4_11
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f94,f83,f102])).

fof(f83,plain,
    ( spl4_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f94,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f44,f85])).

fof(f85,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f91,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f28,f88])).

fof(f28,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

% (8558)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:21:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (8552)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (8557)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (8551)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (8554)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (8565)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (8574)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (8572)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (8554)Refutation not found, incomplete strategy% (8554)------------------------------
% 0.21/0.51  % (8554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8566)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (8560)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (8556)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (8554)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8554)Memory used [KB]: 10618
% 0.21/0.51  % (8554)Time elapsed: 0.091 s
% 0.21/0.51  % (8554)------------------------------
% 0.21/0.51  % (8554)------------------------------
% 0.21/0.51  % (8563)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (8555)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (8573)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (8574)Refutation not found, incomplete strategy% (8574)------------------------------
% 0.21/0.51  % (8574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8570)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.52  % (8564)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (8557)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f51,f56,f61,f71,f76,f81,f86,f91,f106,f107,f120,f125,f130,f135,f147,f153,f155,f161,f167,f175,f186,f200,f209,f224,f251])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    ~spl4_21 | ~spl4_7 | ~spl4_2 | spl4_29),
% 0.21/0.52    inference(avatar_split_clause,[],[f246,f221,f53,f78,f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    spl4_21 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl4_7 <=> v1_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl4_2 <=> v2_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    spl4_29 <=> k9_relat_1(sK2,sK3) = k10_relat_1(k2_funct_1(sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_29),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f245])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    k9_relat_1(sK2,sK3) != k9_relat_1(sK2,sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_29),
% 0.21/0.52    inference(superposition,[],[f223,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    k9_relat_1(sK2,sK3) != k10_relat_1(k2_funct_1(sK2),sK3) | spl4_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f221])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    ~spl4_29 | spl4_24 | ~spl4_27),
% 0.21/0.52    inference(avatar_split_clause,[],[f211,f205,f183,f221])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl4_24 <=> k9_relat_1(sK2,sK3) = k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    spl4_27 <=> k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    k9_relat_1(sK2,sK3) != k10_relat_1(k2_funct_1(sK2),sK3) | (spl4_24 | ~spl4_27)),
% 0.21/0.52    inference(backward_demodulation,[],[f185,f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~spl4_27),
% 0.21/0.52    inference(avatar_component_clause,[],[f205])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    k9_relat_1(sK2,sK3) != k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f183])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ~spl4_7 | ~spl4_18 | ~spl4_19 | spl4_27 | ~spl4_2 | ~spl4_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f203,f109,f53,f205,f150,f144,f78])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    spl4_18 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl4_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl4_12 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl4_12),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f202])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl4_12),
% 0.21/0.52    inference(superposition,[],[f38,f111])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f109])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    spl4_23 | ~spl4_7 | ~spl4_18 | ~spl4_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f199,f150,f144,f78,f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    spl4_23 <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl4_7 | ~spl4_18 | ~spl4_19)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f80,f146,f152,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f150])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f144])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    v1_funct_1(sK2) | ~spl4_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ~spl4_23 | ~spl4_24 | spl4_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f177,f172,f183,f179])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl4_22 <=> k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) = k9_relat_1(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    k9_relat_1(sK2,sK3) != k10_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | spl4_22),
% 0.21/0.52    inference(superposition,[],[f174,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k9_relat_1(sK2,sK3) | spl4_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f172])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    ~spl4_22 | ~spl4_19 | spl4_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f170,f158,f150,f172])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    spl4_20 <=> k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k9_relat_1(sK2,sK3) | (~spl4_19 | spl4_20)),
% 0.21/0.52    inference(backward_demodulation,[],[f160,f169])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | ~spl4_19),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f152,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f158])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl4_21 | ~spl4_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f162,f150,f164])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    v1_relat_1(sK2) | ~spl4_19),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f46,f152,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~spl4_20 | ~spl4_10 | spl4_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f156,f117,f97,f158])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl4_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl4_13 <=> k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (~spl4_10 | spl4_13)),
% 0.21/0.52    inference(forward_demodulation,[],[f119,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f117])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    spl4_12 | ~spl4_10 | ~spl4_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f154,f122,f97,f109])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl4_14 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_10 | ~spl4_14)),
% 0.21/0.52    inference(forward_demodulation,[],[f124,f99])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl4_19 | ~spl4_10 | ~spl4_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f148,f127,f97,f150])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    spl4_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_10 | ~spl4_15)),
% 0.21/0.52    inference(forward_demodulation,[],[f129,f99])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f127])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    spl4_18 | ~spl4_10 | ~spl4_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f142,f132,f97,f144])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl4_16 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_10 | ~spl4_16)),
% 0.21/0.52    inference(forward_demodulation,[],[f134,f99])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f132])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl4_16 | ~spl4_6 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f115,f102,f73,f132])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl4_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    spl4_11 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_6 | ~spl4_11)),
% 0.21/0.52    inference(backward_demodulation,[],[f75,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f102])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl4_15 | ~spl4_5 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f114,f102,f68,f127])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_5 | ~spl4_11)),
% 0.21/0.52    inference(backward_demodulation,[],[f70,f104])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl4_14 | ~spl4_3 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f113,f102,f58,f122])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    spl4_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_3 | ~spl4_11)),
% 0.21/0.52    inference(backward_demodulation,[],[f60,f104])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f58])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ~spl4_13 | spl4_1 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f112,f102,f48,f117])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl4_1 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k8_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (spl4_1 | ~spl4_11)),
% 0.21/0.52    inference(backward_demodulation,[],[f50,f104])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f48])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl4_10 | ~spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f95,f88,f97])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl4_9 <=> l1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_9),
% 0.21/0.52    inference(resolution,[],[f44,f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    l1_struct_0(sK0) | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl4_11 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f94,f83,f102])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl4_8 <=> l1_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_8),
% 0.21/0.52    inference(resolution,[],[f44,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    l1_struct_0(sK1) | ~spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f88])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    l1_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  % (8558)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    (((k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f26,f25,f24,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X3] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_2)).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f83])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    l1_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl4_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f78])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f73])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f32,f68])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f58])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f53])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    v2_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ~spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f48])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (8557)------------------------------
% 0.21/0.52  % (8557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8557)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (8557)Memory used [KB]: 10874
% 0.21/0.52  % (8557)Time elapsed: 0.088 s
% 0.21/0.52  % (8557)------------------------------
% 0.21/0.52  % (8557)------------------------------
% 0.21/0.52  % (8567)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (8550)Success in time 0.162 s
%------------------------------------------------------------------------------
