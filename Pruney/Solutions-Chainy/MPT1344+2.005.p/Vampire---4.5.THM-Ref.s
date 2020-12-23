%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 413 expanded)
%              Number of leaves         :   46 ( 200 expanded)
%              Depth                    :   10
%              Number of atoms          :  782 (1854 expanded)
%              Number of equality atoms :  138 ( 397 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f694,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f85,f90,f95,f100,f105,f125,f143,f159,f163,f219,f227,f255,f311,f361,f367,f373,f408,f421,f448,f518,f551,f562,f605,f633,f649,f681,f688,f693])).

fof(f693,plain,
    ( spl4_61
    | ~ spl4_65 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | spl4_61
    | ~ spl4_65 ),
    inference(trivial_inequality_removal,[],[f690])).

fof(f690,plain,
    ( k10_relat_1(sK2,sK3) != k10_relat_1(sK2,sK3)
    | spl4_61
    | ~ spl4_65 ),
    inference(superposition,[],[f632,f687])).

fof(f687,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f686])).

fof(f686,plain,
    ( spl4_65
  <=> ! [X0] : k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f632,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) != k10_relat_1(sK2,sK3)
    | spl4_61 ),
    inference(avatar_component_clause,[],[f630])).

fof(f630,plain,
    ( spl4_61
  <=> k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) = k10_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f688,plain,
    ( spl4_65
    | ~ spl4_54
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f684,f679,f549,f686])).

fof(f549,plain,
    ( spl4_54
  <=> ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f679,plain,
    ( spl4_64
  <=> ! [X10] : k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(sK2,X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f684,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)
    | ~ spl4_54
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f550,f680])).

fof(f680,plain,
    ( ! [X10] : k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(sK2,X10)
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f679])).

fof(f550,plain,
    ( ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f549])).

fof(f681,plain,
    ( spl4_64
    | ~ spl4_12
    | ~ spl4_25
    | ~ spl4_29
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f677,f559,f286,f216,f122,f679])).

fof(f122,plain,
    ( spl4_12
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f216,plain,
    ( spl4_25
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f286,plain,
    ( spl4_29
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f559,plain,
    ( spl4_56
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f677,plain,
    ( ! [X10] : k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(sK2,X10)
    | ~ spl4_12
    | ~ spl4_25
    | ~ spl4_29
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f676,f124])).

fof(f124,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f676,plain,
    ( ! [X10] : k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X10)
    | ~ spl4_25
    | ~ spl4_29
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f675,f561])).

fof(f561,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f559])).

fof(f675,plain,
    ( ! [X10] :
        ( k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X10)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_25
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f673,f218])).

fof(f218,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f216])).

fof(f673,plain,
    ( ! [X10] :
        ( k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X10)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl4_29 ),
    inference(resolution,[],[f287,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f287,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f286])).

fof(f649,plain,
    ( spl4_29
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_42
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f646,f596,f405,f370,f364,f358,f92,f67,f286])).

fof(f67,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f92,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f358,plain,
    ( spl4_38
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f364,plain,
    ( spl4_39
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f370,plain,
    ( spl4_40
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f405,plain,
    ( spl4_42
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f596,plain,
    ( spl4_59
  <=> ! [X1] :
        ( ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))
        | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f646,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_42
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f645,f407])).

fof(f407,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f405])).

fof(f645,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f644,f94])).

fof(f94,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f644,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f643,f69])).

fof(f69,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f643,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_38
    | ~ spl4_39
    | ~ spl4_40
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f642,f366])).

fof(f366,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f364])).

fof(f642,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_38
    | ~ spl4_40
    | ~ spl4_59 ),
    inference(subsumption_resolution,[],[f641,f372])).

fof(f372,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f370])).

fof(f641,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_38
    | ~ spl4_59 ),
    inference(trivial_inequality_removal,[],[f640])).

fof(f640,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_38
    | ~ spl4_59 ),
    inference(superposition,[],[f597,f360])).

fof(f360,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f358])).

fof(f597,plain,
    ( ! [X1] :
        ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))
        | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1) )
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f596])).

fof(f633,plain,
    ( ~ spl4_61
    | ~ spl4_16
    | spl4_31
    | ~ spl4_42
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f628,f446,f405,f308,f156,f630])).

fof(f156,plain,
    ( spl4_16
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f308,plain,
    ( spl4_31
  <=> k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f446,plain,
    ( spl4_46
  <=> ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f628,plain,
    ( k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) != k10_relat_1(sK2,sK3)
    | ~ spl4_16
    | spl4_31
    | ~ spl4_42
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f627,f447])).

fof(f447,plain,
    ( ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X1)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f446])).

fof(f627,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3)
    | ~ spl4_16
    | spl4_31
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f626,f407])).

fof(f626,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | ~ spl4_16
    | spl4_31 ),
    inference(forward_demodulation,[],[f310,f158])).

fof(f158,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f310,plain,
    ( k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_31 ),
    inference(avatar_component_clause,[],[f308])).

fof(f605,plain,
    ( spl4_59
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f604,f516,f140,f97,f596])).

fof(f97,plain,
    ( spl4_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f140,plain,
    ( spl4_13
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f516,plain,
    ( spl4_52
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1)
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1))
        | ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f604,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0))
        | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f603,f142])).

fof(f142,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f603,plain,
    ( ! [X0] :
        ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0))
        | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(sK1)) )
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f602,f142])).

fof(f602,plain,
    ( ! [X0] :
        ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(sK1)) )
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f601,f142])).

fof(f601,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0)
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(sK1)) )
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f599,f142])).

fof(f599,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
        | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0)
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(sK1)) )
    | ~ spl4_8
    | ~ spl4_52 ),
    inference(resolution,[],[f517,f99])).

fof(f99,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f517,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1)
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1))
        | ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) )
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f516])).

fof(f562,plain,
    ( spl4_56
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f557,f418,f559])).

fof(f418,plain,
    ( spl4_44
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f557,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_44 ),
    inference(subsumption_resolution,[],[f547,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f547,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))
    | ~ spl4_44 ),
    inference(resolution,[],[f420,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f420,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f418])).

fof(f551,plain,
    ( spl4_54
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f538,f418,f549])).

fof(f538,plain,
    ( ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)
    | ~ spl4_44 ),
    inference(resolution,[],[f420,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f518,plain,
    ( spl4_52
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f514,f161,f156,f516])).

fof(f161,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),X1))
        | ~ v2_funct_1(X1)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f514,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1)
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1))
        | ~ v2_funct_1(X1)
        | ~ v1_funct_1(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f513,f158])).

fof(f513,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
        | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1)
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1))
        | ~ v2_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f512,f158])).

fof(f512,plain,
    ( ! [X0,X1] :
        ( k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1)
        | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1))
        | ~ v2_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f511,f158])).

fof(f511,plain,
    ( ! [X0,X1] :
        ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1))
        | ~ v2_funct_1(X1)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f162,f158])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),X1))
        | ~ v2_funct_1(X1)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f448,plain,
    ( spl4_46
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f436,f364,f446])).

fof(f436,plain,
    ( ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X1)
    | ~ spl4_39 ),
    inference(resolution,[],[f366,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f421,plain,
    ( ~ spl4_39
    | ~ spl4_38
    | spl4_44
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f416,f370,f92,f67,f418,f358,f364])).

fof(f416,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f415,f94])).

fof(f415,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f401,f69])).

fof(f401,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_40 ),
    inference(resolution,[],[f372,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

% (29100)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
fof(f408,plain,
    ( ~ spl4_39
    | ~ spl4_38
    | spl4_42
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f403,f370,f92,f67,f405,f358,f364])).

fof(f403,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f402,f94])).

fof(f402,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_40 ),
    inference(subsumption_resolution,[],[f395,f69])).

fof(f395,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_40 ),
    inference(resolution,[],[f372,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f373,plain,
    ( spl4_40
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f368,f156,f140,f87,f370])).

fof(f87,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f368,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f341,f142])).

fof(f341,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(superposition,[],[f89,f158])).

fof(f89,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f367,plain,
    ( spl4_39
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f362,f156,f140,f82,f364])).

fof(f82,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f362,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f340,f142])).

fof(f340,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_16 ),
    inference(superposition,[],[f84,f158])).

fof(f84,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f361,plain,
    ( spl4_38
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f356,f156,f140,f72,f358])).

fof(f72,plain,
    ( spl4_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f356,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f339,f142])).

fof(f339,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(superposition,[],[f74,f158])).

fof(f74,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f311,plain,
    ( ~ spl4_31
    | spl4_1
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f293,f140,f62,f308])).

fof(f62,plain,
    ( spl4_1
  <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f293,plain,
    ( k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_1
    | ~ spl4_13 ),
    inference(superposition,[],[f64,f142])).

fof(f64,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f255,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f254,f82,f114])).

fof(f114,plain,
    ( spl4_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f254,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f240,f59])).

fof(f240,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(resolution,[],[f84,f60])).

fof(f227,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f219,plain,
    ( ~ spl4_5
    | ~ spl4_21
    | spl4_25
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f214,f92,f87,f67,f216,f193,f82])).

fof(f193,plain,
    ( spl4_21
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f214,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f213,f94])).

fof(f213,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f185,f69])).

fof(f185,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f163,plain,
    ( spl4_17
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f153,f102,f161])).

fof(f102,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),X1))
        | ~ v2_funct_1(X1)
        | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f104,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(f104,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f159,plain,
    ( spl4_16
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f152,f102,f156])).

fof(f152,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f104,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f143,plain,
    ( spl4_13
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f136,f97,f140])).

% (29101)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f136,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f99,f53])).

fof(f125,plain,
    ( ~ spl4_10
    | ~ spl4_7
    | spl4_12
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f112,f67,f122,f92,f114])).

fof(f112,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f105,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f37,f102])).

fof(f37,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f35,f34,f33,f32])).

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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

fof(f35,plain,
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

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f100,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f38,f97])).

fof(f38,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f39,f92])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f40,f87])).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f43,f72])).

fof(f43,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f67])).

fof(f44,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f45,f62])).

fof(f45,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (29105)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (29113)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.48  % (29115)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.49  % (29107)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.49  % (29105)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (29116)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f694,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f65,f70,f75,f85,f90,f95,f100,f105,f125,f143,f159,f163,f219,f227,f255,f311,f361,f367,f373,f408,f421,f448,f518,f551,f562,f605,f633,f649,f681,f688,f693])).
% 0.20/0.50  fof(f693,plain,(
% 0.20/0.50    spl4_61 | ~spl4_65),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f692])).
% 0.20/0.50  fof(f692,plain,(
% 0.20/0.50    $false | (spl4_61 | ~spl4_65)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f690])).
% 0.20/0.50  fof(f690,plain,(
% 0.20/0.50    k10_relat_1(sK2,sK3) != k10_relat_1(sK2,sK3) | (spl4_61 | ~spl4_65)),
% 0.20/0.50    inference(superposition,[],[f632,f687])).
% 0.20/0.50  fof(f687,plain,(
% 0.20/0.50    ( ! [X0] : (k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)) ) | ~spl4_65),
% 0.20/0.50    inference(avatar_component_clause,[],[f686])).
% 0.20/0.50  fof(f686,plain,(
% 0.20/0.50    spl4_65 <=> ! [X0] : k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.20/0.50  fof(f632,plain,(
% 0.20/0.50    k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) != k10_relat_1(sK2,sK3) | spl4_61),
% 0.20/0.50    inference(avatar_component_clause,[],[f630])).
% 0.20/0.50  fof(f630,plain,(
% 0.20/0.50    spl4_61 <=> k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) = k10_relat_1(sK2,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.20/0.50  fof(f688,plain,(
% 0.20/0.50    spl4_65 | ~spl4_54 | ~spl4_64),
% 0.20/0.50    inference(avatar_split_clause,[],[f684,f679,f549,f686])).
% 0.20/0.50  fof(f549,plain,(
% 0.20/0.50    spl4_54 <=> ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 0.20/0.50  fof(f679,plain,(
% 0.20/0.50    spl4_64 <=> ! [X10] : k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(sK2,X10)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.20/0.50  fof(f684,plain,(
% 0.20/0.50    ( ! [X0] : (k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)) ) | (~spl4_54 | ~spl4_64)),
% 0.20/0.50    inference(forward_demodulation,[],[f550,f680])).
% 0.20/0.50  fof(f680,plain,(
% 0.20/0.50    ( ! [X10] : (k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(sK2,X10)) ) | ~spl4_64),
% 0.20/0.50    inference(avatar_component_clause,[],[f679])).
% 0.20/0.50  fof(f550,plain,(
% 0.20/0.50    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)) ) | ~spl4_54),
% 0.20/0.50    inference(avatar_component_clause,[],[f549])).
% 0.20/0.50  fof(f681,plain,(
% 0.20/0.50    spl4_64 | ~spl4_12 | ~spl4_25 | ~spl4_29 | ~spl4_56),
% 0.20/0.50    inference(avatar_split_clause,[],[f677,f559,f286,f216,f122,f679])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    spl4_12 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    spl4_25 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    spl4_29 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.20/0.50  fof(f559,plain,(
% 0.20/0.50    spl4_56 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.20/0.50  fof(f677,plain,(
% 0.20/0.50    ( ! [X10] : (k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(sK2,X10)) ) | (~spl4_12 | ~spl4_25 | ~spl4_29 | ~spl4_56)),
% 0.20/0.50    inference(forward_demodulation,[],[f676,f124])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl4_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f122])).
% 0.20/0.50  fof(f676,plain,(
% 0.20/0.50    ( ! [X10] : (k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X10)) ) | (~spl4_25 | ~spl4_29 | ~spl4_56)),
% 0.20/0.50    inference(subsumption_resolution,[],[f675,f561])).
% 0.20/0.50  fof(f561,plain,(
% 0.20/0.50    v1_relat_1(k2_funct_1(sK2)) | ~spl4_56),
% 0.20/0.50    inference(avatar_component_clause,[],[f559])).
% 0.20/0.50  fof(f675,plain,(
% 0.20/0.50    ( ! [X10] : (k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X10) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl4_25 | ~spl4_29)),
% 0.20/0.50    inference(subsumption_resolution,[],[f673,f218])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    v1_funct_1(k2_funct_1(sK2)) | ~spl4_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f216])).
% 0.20/0.50  fof(f673,plain,(
% 0.20/0.50    ( ! [X10] : (k9_relat_1(k2_funct_1(sK2),X10) = k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X10) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl4_29),
% 0.20/0.50    inference(resolution,[],[f287,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    v2_funct_1(k2_funct_1(sK2)) | ~spl4_29),
% 0.20/0.50    inference(avatar_component_clause,[],[f286])).
% 0.20/0.50  fof(f649,plain,(
% 0.20/0.50    spl4_29 | ~spl4_2 | ~spl4_7 | ~spl4_38 | ~spl4_39 | ~spl4_40 | ~spl4_42 | ~spl4_59),
% 0.20/0.50    inference(avatar_split_clause,[],[f646,f596,f405,f370,f364,f358,f92,f67,f286])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    spl4_2 <=> v2_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    spl4_7 <=> v1_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.50  fof(f358,plain,(
% 0.20/0.50    spl4_38 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.50  fof(f364,plain,(
% 0.20/0.50    spl4_39 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.50  fof(f370,plain,(
% 0.20/0.50    spl4_40 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.20/0.50  fof(f405,plain,(
% 0.20/0.50    spl4_42 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.20/0.50  fof(f596,plain,(
% 0.20/0.50    spl4_59 <=> ! [X1] : (~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(X1) | ~v1_funct_1(X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.20/0.50  fof(f646,plain,(
% 0.20/0.50    v2_funct_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_7 | ~spl4_38 | ~spl4_39 | ~spl4_40 | ~spl4_42 | ~spl4_59)),
% 0.20/0.50    inference(forward_demodulation,[],[f645,f407])).
% 0.20/0.50  fof(f407,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_42),
% 0.20/0.50    inference(avatar_component_clause,[],[f405])).
% 0.20/0.50  fof(f645,plain,(
% 0.20/0.50    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl4_2 | ~spl4_7 | ~spl4_38 | ~spl4_39 | ~spl4_40 | ~spl4_59)),
% 0.20/0.50    inference(subsumption_resolution,[],[f644,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    v1_funct_1(sK2) | ~spl4_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f92])).
% 0.20/0.50  fof(f644,plain,(
% 0.20/0.50    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~v1_funct_1(sK2) | (~spl4_2 | ~spl4_38 | ~spl4_39 | ~spl4_40 | ~spl4_59)),
% 0.20/0.50    inference(subsumption_resolution,[],[f643,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    v2_funct_1(sK2) | ~spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f67])).
% 0.20/0.50  fof(f643,plain,(
% 0.20/0.50    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl4_38 | ~spl4_39 | ~spl4_40 | ~spl4_59)),
% 0.20/0.50    inference(subsumption_resolution,[],[f642,f366])).
% 0.20/0.50  fof(f366,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f364])).
% 0.20/0.50  fof(f642,plain,(
% 0.20/0.50    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl4_38 | ~spl4_40 | ~spl4_59)),
% 0.20/0.50    inference(subsumption_resolution,[],[f641,f372])).
% 0.20/0.50  fof(f372,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_40),
% 0.20/0.50    inference(avatar_component_clause,[],[f370])).
% 0.20/0.50  fof(f641,plain,(
% 0.20/0.50    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl4_38 | ~spl4_59)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f640])).
% 0.20/0.50  fof(f640,plain,(
% 0.20/0.50    k2_struct_0(sK1) != k2_struct_0(sK1) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl4_38 | ~spl4_59)),
% 0.20/0.50    inference(superposition,[],[f597,f360])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f358])).
% 0.20/0.50  fof(f597,plain,(
% 0.20/0.50    ( ! [X1] : (k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(X1) | ~v1_funct_1(X1)) ) | ~spl4_59),
% 0.20/0.50    inference(avatar_component_clause,[],[f596])).
% 0.20/0.50  fof(f633,plain,(
% 0.20/0.50    ~spl4_61 | ~spl4_16 | spl4_31 | ~spl4_42 | ~spl4_46),
% 0.20/0.50    inference(avatar_split_clause,[],[f628,f446,f405,f308,f156,f630])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    spl4_16 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    spl4_31 <=> k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.50  fof(f446,plain,(
% 0.20/0.50    spl4_46 <=> ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.20/0.50  fof(f628,plain,(
% 0.20/0.50    k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) != k10_relat_1(sK2,sK3) | (~spl4_16 | spl4_31 | ~spl4_42 | ~spl4_46)),
% 0.20/0.50    inference(forward_demodulation,[],[f627,f447])).
% 0.20/0.50  fof(f447,plain,(
% 0.20/0.50    ( ! [X1] : (k10_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X1)) ) | ~spl4_46),
% 0.20/0.50    inference(avatar_component_clause,[],[f446])).
% 0.20/0.50  fof(f627,plain,(
% 0.20/0.50    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) | (~spl4_16 | spl4_31 | ~spl4_42)),
% 0.20/0.50    inference(forward_demodulation,[],[f626,f407])).
% 0.20/0.50  fof(f626,plain,(
% 0.20/0.50    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (~spl4_16 | spl4_31)),
% 0.20/0.50    inference(forward_demodulation,[],[f310,f158])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f156])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f308])).
% 0.20/0.50  fof(f605,plain,(
% 0.20/0.50    spl4_59 | ~spl4_8 | ~spl4_13 | ~spl4_52),
% 0.20/0.50    inference(avatar_split_clause,[],[f604,f516,f140,f97,f596])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    spl4_8 <=> l1_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    spl4_13 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.50  fof(f516,plain,(
% 0.20/0.50    spl4_52 <=> ! [X1,X0] : (~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~l1_struct_0(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.20/0.50  fof(f604,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) ) | (~spl4_8 | ~spl4_13 | ~spl4_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f603,f142])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f140])).
% 0.20/0.50  fof(f603,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(sK1))) ) | (~spl4_8 | ~spl4_13 | ~spl4_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f602,f142])).
% 0.20/0.50  fof(f602,plain,(
% 0.20/0.50    ( ! [X0] : (k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(sK1))) ) | (~spl4_8 | ~spl4_13 | ~spl4_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f601,f142])).
% 0.20/0.50  fof(f601,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(sK1))) ) | (~spl4_8 | ~spl4_13 | ~spl4_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f599,f142])).
% 0.20/0.50  fof(f599,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(sK1))) ) | (~spl4_8 | ~spl4_52)),
% 0.20/0.50    inference(resolution,[],[f517,f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    l1_struct_0(sK1) | ~spl4_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f97])).
% 0.20/0.50  fof(f517,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))) ) | ~spl4_52),
% 0.20/0.50    inference(avatar_component_clause,[],[f516])).
% 0.20/0.50  fof(f562,plain,(
% 0.20/0.50    spl4_56 | ~spl4_44),
% 0.20/0.50    inference(avatar_split_clause,[],[f557,f418,f559])).
% 0.20/0.50  fof(f418,plain,(
% 0.20/0.50    spl4_44 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.20/0.50  fof(f557,plain,(
% 0.20/0.50    v1_relat_1(k2_funct_1(sK2)) | ~spl4_44),
% 0.20/0.50    inference(subsumption_resolution,[],[f547,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f547,plain,(
% 0.20/0.50    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))) | ~spl4_44),
% 0.20/0.50    inference(resolution,[],[f420,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f420,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl4_44),
% 0.20/0.50    inference(avatar_component_clause,[],[f418])).
% 0.20/0.50  fof(f551,plain,(
% 0.20/0.50    spl4_54 | ~spl4_44),
% 0.20/0.50    inference(avatar_split_clause,[],[f538,f418,f549])).
% 0.20/0.50  fof(f538,plain,(
% 0.20/0.50    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)) ) | ~spl4_44),
% 0.20/0.50    inference(resolution,[],[f420,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.50  fof(f518,plain,(
% 0.20/0.50    spl4_52 | ~spl4_16 | ~spl4_17),
% 0.20/0.50    inference(avatar_split_clause,[],[f514,f161,f156,f516])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    spl4_17 <=> ! [X1,X0] : (v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),X1)) | ~v2_funct_1(X1) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_struct_0(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.50  fof(f514,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~l1_struct_0(X0)) ) | (~spl4_16 | ~spl4_17)),
% 0.20/0.50    inference(forward_demodulation,[],[f513,f158])).
% 0.20/0.50  fof(f513,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1)) | ~v2_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_struct_0(X0)) ) | (~spl4_16 | ~spl4_17)),
% 0.20/0.50    inference(forward_demodulation,[],[f512,f158])).
% 0.20/0.50  fof(f512,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_struct_0(X0) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1)) | ~v2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_struct_0(X0)) ) | (~spl4_16 | ~spl4_17)),
% 0.20/0.50    inference(forward_demodulation,[],[f511,f158])).
% 0.20/0.50  fof(f511,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0),X1)) | ~v2_funct_1(X1) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_struct_0(X0)) ) | (~spl4_16 | ~spl4_17)),
% 0.20/0.50    inference(forward_demodulation,[],[f162,f158])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),X1)) | ~v2_funct_1(X1) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_struct_0(X0)) ) | ~spl4_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f161])).
% 0.20/0.50  fof(f448,plain,(
% 0.20/0.50    spl4_46 | ~spl4_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f436,f364,f446])).
% 0.20/0.50  fof(f436,plain,(
% 0.20/0.50    ( ! [X1] : (k10_relat_1(sK2,X1) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X1)) ) | ~spl4_39),
% 0.20/0.50    inference(resolution,[],[f366,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.50  fof(f421,plain,(
% 0.20/0.50    ~spl4_39 | ~spl4_38 | spl4_44 | ~spl4_2 | ~spl4_7 | ~spl4_40),
% 0.20/0.50    inference(avatar_split_clause,[],[f416,f370,f92,f67,f418,f358,f364])).
% 0.20/0.50  fof(f416,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_2 | ~spl4_7 | ~spl4_40)),
% 0.20/0.50    inference(subsumption_resolution,[],[f415,f94])).
% 0.20/0.50  fof(f415,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | (~spl4_2 | ~spl4_40)),
% 0.20/0.50    inference(subsumption_resolution,[],[f401,f69])).
% 0.20/0.50  fof(f401,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~spl4_40),
% 0.20/0.50    inference(resolution,[],[f372,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.50  % (29100)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  fof(f408,plain,(
% 0.20/0.50    ~spl4_39 | ~spl4_38 | spl4_42 | ~spl4_2 | ~spl4_7 | ~spl4_40),
% 0.20/0.50    inference(avatar_split_clause,[],[f403,f370,f92,f67,f405,f358,f364])).
% 0.20/0.50  fof(f403,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_2 | ~spl4_7 | ~spl4_40)),
% 0.20/0.50    inference(subsumption_resolution,[],[f402,f94])).
% 0.20/0.50  fof(f402,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | (~spl4_2 | ~spl4_40)),
% 0.20/0.50    inference(subsumption_resolution,[],[f395,f69])).
% 0.20/0.50  fof(f395,plain,(
% 0.20/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~spl4_40),
% 0.20/0.50    inference(resolution,[],[f372,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.50  fof(f373,plain,(
% 0.20/0.50    spl4_40 | ~spl4_6 | ~spl4_13 | ~spl4_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f368,f156,f140,f87,f370])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl4_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f368,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_6 | ~spl4_13 | ~spl4_16)),
% 0.20/0.50    inference(forward_demodulation,[],[f341,f142])).
% 0.20/0.50  fof(f341,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl4_6 | ~spl4_16)),
% 0.20/0.50    inference(superposition,[],[f89,f158])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f87])).
% 0.20/0.50  fof(f367,plain,(
% 0.20/0.50    spl4_39 | ~spl4_5 | ~spl4_13 | ~spl4_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f362,f156,f140,f82,f364])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_5 | ~spl4_13 | ~spl4_16)),
% 0.20/0.50    inference(forward_demodulation,[],[f340,f142])).
% 0.20/0.50  fof(f340,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | (~spl4_5 | ~spl4_16)),
% 0.20/0.50    inference(superposition,[],[f84,f158])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f82])).
% 0.20/0.50  fof(f361,plain,(
% 0.20/0.50    spl4_38 | ~spl4_3 | ~spl4_13 | ~spl4_16),
% 0.20/0.50    inference(avatar_split_clause,[],[f356,f156,f140,f72,f358])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl4_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f356,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_3 | ~spl4_13 | ~spl4_16)),
% 0.20/0.50    inference(forward_demodulation,[],[f339,f142])).
% 0.20/0.50  fof(f339,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl4_3 | ~spl4_16)),
% 0.20/0.50    inference(superposition,[],[f74,f158])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f72])).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    ~spl4_31 | spl4_1 | ~spl4_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f293,f140,f62,f308])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl4_1 <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (spl4_1 | ~spl4_13)),
% 0.20/0.50    inference(superposition,[],[f64,f142])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f62])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    spl4_10 | ~spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f254,f82,f114])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    spl4_10 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.50  fof(f254,plain,(
% 0.20/0.50    v1_relat_1(sK2) | ~spl4_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f240,f59])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl4_5),
% 0.20/0.50    inference(resolution,[],[f84,f60])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f219,plain,(
% 0.20/0.50    ~spl4_5 | ~spl4_21 | spl4_25 | ~spl4_2 | ~spl4_6 | ~spl4_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f214,f92,f87,f67,f216,f193,f82])).
% 0.20/0.50  fof(f193,plain,(
% 0.20/0.50    spl4_21 <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.50  fof(f214,plain,(
% 0.20/0.50    v1_funct_1(k2_funct_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl4_2 | ~spl4_6 | ~spl4_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f213,f94])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    v1_funct_1(k2_funct_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | (~spl4_2 | ~spl4_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f185,f69])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    v1_funct_1(k2_funct_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~spl4_6),
% 0.20/0.50    inference(resolution,[],[f89,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    spl4_17 | ~spl4_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f153,f102,f161])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    spl4_9 <=> l1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),X1)) | ~v2_funct_1(X1) | k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_struct_0(X0)) ) | ~spl4_9),
% 0.20/0.50    inference(resolution,[],[f104,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl4_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f102])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    spl4_16 | ~spl4_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f152,f102,f156])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_9),
% 0.20/0.50    inference(resolution,[],[f104,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    spl4_13 | ~spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f136,f97,f140])).
% 0.20/0.50  % (29101)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_8),
% 0.20/0.50    inference(resolution,[],[f99,f53])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    ~spl4_10 | ~spl4_7 | spl4_12 | ~spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f112,f67,f122,f92,f114])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 0.20/0.50    inference(resolution,[],[f69,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    spl4_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f102])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    l1_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    (((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f35,f34,f33,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    spl4_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f97])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    l1_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl4_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f92])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f87])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f41,f82])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f72])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f44,f67])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    v2_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f62])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (29114)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (29105)------------------------------
% 0.20/0.51  % (29105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29105)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (29105)Memory used [KB]: 6652
% 0.20/0.51  % (29105)Time elapsed: 0.086 s
% 0.20/0.51  % (29105)------------------------------
% 0.20/0.51  % (29105)------------------------------
% 0.20/0.51  % (29101)Refutation not found, incomplete strategy% (29101)------------------------------
% 0.20/0.51  % (29101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29101)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29101)Memory used [KB]: 10618
% 0.20/0.51  % (29101)Time elapsed: 0.093 s
% 0.20/0.51  % (29101)------------------------------
% 0.20/0.51  % (29101)------------------------------
% 0.20/0.51  % (29097)Success in time 0.152 s
%------------------------------------------------------------------------------
