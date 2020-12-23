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
% DateTime   : Thu Dec  3 13:14:07 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 360 expanded)
%              Number of leaves         :   38 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  610 (1212 expanded)
%              Number of equality atoms :  152 ( 324 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f109,f114,f119,f124,f129,f146,f152,f160,f173,f181,f184,f194,f201,f208,f232,f246,f253,f266,f271,f275,f281])).

fof(f281,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_26
    | spl3_28 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_26
    | spl3_28 ),
    inference(subsumption_resolution,[],[f279,f270])).

fof(f270,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl3_28
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f279,plain,
    ( k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f278,f200])).

fof(f200,plain,
    ( k2_struct_0(sK1) = k9_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_20
  <=> k2_struct_0(sK1) = k9_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f278,plain,
    ( k9_relat_1(sK2,k2_struct_0(sK0)) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f259,f261])).

fof(f261,plain,
    ( ! [X1] : k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1) = k9_relat_1(sK2,X1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f255,f185])).

fof(f185,plain,
    ( ! [X7] : k9_relat_1(sK2,X7) = k10_relat_1(k2_funct_1(sK2),X7)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f102,f179])).

fof(f179,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_17
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f102,plain,
    ( ! [X7] :
        ( ~ v1_relat_1(sK2)
        | k9_relat_1(sK2,X7) = k10_relat_1(k2_funct_1(sK2),X7) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f97,f71])).

fof(f71,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f97,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | k9_relat_1(sK2,X7) = k10_relat_1(k2_funct_1(sK2),X7) )
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ),
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f76,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f255,plain,
    ( ! [X1] : k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1) = k10_relat_1(k2_funct_1(sK2),X1)
    | ~ spl3_26 ),
    inference(resolution,[],[f252,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f252,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl3_26
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f259,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),k2_struct_0(sK0))
    | ~ spl3_26 ),
    inference(resolution,[],[f252,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f275,plain,
    ( ~ spl3_16
    | ~ spl3_21
    | ~ spl3_26
    | spl3_27 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl3_16
    | ~ spl3_21
    | ~ spl3_26
    | spl3_27 ),
    inference(subsumption_resolution,[],[f273,f265])).

fof(f265,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_27 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl3_27
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f273,plain,
    ( k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_16
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f272,f207])).

fof(f207,plain,
    ( k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl3_21
  <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f272,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f258,f260])).

fof(f260,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f254,f176])).

fof(f176,plain,
    ( ! [X6] : k10_relat_1(sK2,X6) = k9_relat_1(k2_funct_1(sK2),X6)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_16
  <=> ! [X6] : k10_relat_1(sK2,X6) = k9_relat_1(k2_funct_1(sK2),X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f254,plain,
    ( ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)
    | ~ spl3_26 ),
    inference(resolution,[],[f252,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f258,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),k2_struct_0(sK1))
    | ~ spl3_26 ),
    inference(resolution,[],[f252,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f271,plain,
    ( ~ spl3_28
    | spl3_14
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f248,f243,f166,f268])).

fof(f166,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f243,plain,
    ( spl3_25
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f248,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_14
    | ~ spl3_25 ),
    inference(superposition,[],[f168,f245])).

fof(f245,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f243])).

fof(f168,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f166])).

fof(f266,plain,
    ( ~ spl3_27
    | spl3_15
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f247,f243,f170,f263])).

fof(f170,plain,
    ( spl3_15
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f247,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | spl3_15
    | ~ spl3_25 ),
    inference(superposition,[],[f172,f245])).

fof(f172,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f253,plain,
    ( spl3_26
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f241,f149,f143,f131,f74,f69,f250])).

fof(f131,plain,
    ( spl3_11
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f143,plain,
    ( spl3_12
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f149,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f241,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f240,f133])).

fof(f133,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f240,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f239,f145])).

fof(f145,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f239,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f100,f151])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f100,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_2(sK2,X4,X5)
        | k2_relset_1(X4,X5,sK2) != X5
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X4))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f95,f71])).

fof(f95,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(sK2,X4,X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(sK2)
        | k2_relset_1(X4,X5,sK2) != X5
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X4))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f246,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f238,f149,f143,f131,f74,f69,f243])).

fof(f238,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f237,f133])).

fof(f237,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f236,f145])).

fof(f236,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f98,f151])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f93,f71])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_1(sK2)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f232,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f230,f81])).

fof(f81,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f230,plain,
    ( v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f229,f86])).

fof(f86,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f229,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f228,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f228,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_19 ),
    inference(superposition,[],[f45,f193])).

fof(f193,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_19
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f208,plain,
    ( spl3_21
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f203,f187,f149,f205])).

fof(f187,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f203,plain,
    ( k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f202,f189])).

fof(f189,plain,
    ( k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f202,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k10_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f158,f154])).

fof(f154,plain,
    ( ! [X1] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1)
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f61])).

fof(f158,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f50])).

fof(f201,plain,
    ( spl3_20
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f196,f149,f131,f198])).

fof(f196,plain,
    ( k2_struct_0(sK1) = k9_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f195,f133])).

fof(f195,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f157,f153])).

fof(f153,plain,
    ( ! [X0] : k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f62])).

fof(f157,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f49])).

fof(f194,plain,
    ( spl3_18
    | spl3_19
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f159,f149,f143,f191,f187])).

fof(f159,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f156,f145])).

fof(f156,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f184,plain,
    ( ~ spl3_13
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl3_13
    | spl3_17 ),
    inference(resolution,[],[f182,f151])).

fof(f182,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_17 ),
    inference(resolution,[],[f180,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f180,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f178])).

fof(f181,plain,
    ( spl3_16
    | ~ spl3_17
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f101,f74,f69,f178,f175])).

fof(f101,plain,
    ( ! [X6] :
        ( ~ v1_relat_1(sK2)
        | k10_relat_1(sK2,X6) = k9_relat_1(k2_funct_1(sK2),X6) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f96,f71])).

fof(f96,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | k10_relat_1(sK2,X6) = k9_relat_1(k2_funct_1(sK2),X6) )
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f173,plain,
    ( ~ spl3_14
    | ~ spl3_15
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f164,f121,f111,f170,f166])).

fof(f111,plain,
    ( spl3_7
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f121,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f164,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f163,f123])).

fof(f123,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f163,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f162,f113])).

fof(f113,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f162,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f161,f123])).

fof(f161,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f34,f113])).

fof(f34,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f160,plain,
    ( spl3_11
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f141,f126,f121,f111,f131])).

fof(f126,plain,
    ( spl3_10
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f141,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f136,f123])).

fof(f136,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f128,f113])).

fof(f128,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f152,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f139,f121,f116,f111,f149])).

fof(f116,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f135,f123])).

fof(f135,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f118,f113])).

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f146,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f138,f121,f111,f106,f143])).

fof(f106,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f138,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f137,f113])).

fof(f137,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f108,f123])).

fof(f108,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f129,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f38,f126])).

fof(f38,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f124,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f104,f89,f121])).

fof(f89,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f104,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f91,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f91,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f119,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f37,f116])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f114,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f103,f84,f111])).

fof(f103,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f86,f44])).

fof(f109,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f36,f106])).

fof(f36,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f92,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f42,f89])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (1226670080)
% 0.13/0.36  ipcrm: permission denied for id (1226735618)
% 0.20/0.36  ipcrm: permission denied for id (1226866695)
% 0.20/0.37  ipcrm: permission denied for id (1226932233)
% 0.20/0.37  ipcrm: permission denied for id (1227030540)
% 0.20/0.37  ipcrm: permission denied for id (1227063309)
% 0.20/0.37  ipcrm: permission denied for id (1227096078)
% 0.20/0.38  ipcrm: permission denied for id (1227194385)
% 0.20/0.38  ipcrm: permission denied for id (1227259923)
% 0.20/0.38  ipcrm: permission denied for id (1227423768)
% 0.20/0.39  ipcrm: permission denied for id (1227587613)
% 0.20/0.39  ipcrm: permission denied for id (1227620382)
% 0.20/0.39  ipcrm: permission denied for id (1227685920)
% 0.20/0.39  ipcrm: permission denied for id (1227784227)
% 0.20/0.40  ipcrm: permission denied for id (1227849765)
% 0.20/0.40  ipcrm: permission denied for id (1227882534)
% 0.20/0.40  ipcrm: permission denied for id (1227948072)
% 0.20/0.40  ipcrm: permission denied for id (1227980841)
% 0.20/0.40  ipcrm: permission denied for id (1228046379)
% 0.20/0.41  ipcrm: permission denied for id (1228079148)
% 0.20/0.41  ipcrm: permission denied for id (1228111917)
% 0.20/0.41  ipcrm: permission denied for id (1228210223)
% 0.20/0.41  ipcrm: permission denied for id (1228242992)
% 0.20/0.41  ipcrm: permission denied for id (1228275761)
% 0.20/0.41  ipcrm: permission denied for id (1228308530)
% 0.20/0.42  ipcrm: permission denied for id (1228439606)
% 0.20/0.42  ipcrm: permission denied for id (1228505144)
% 0.20/0.42  ipcrm: permission denied for id (1228570682)
% 0.20/0.42  ipcrm: permission denied for id (1228603451)
% 0.20/0.42  ipcrm: permission denied for id (1228636220)
% 0.20/0.43  ipcrm: permission denied for id (1228668989)
% 0.20/0.43  ipcrm: permission denied for id (1228701758)
% 0.20/0.43  ipcrm: permission denied for id (1228767296)
% 0.20/0.43  ipcrm: permission denied for id (1228800065)
% 0.20/0.43  ipcrm: permission denied for id (1228832834)
% 0.20/0.44  ipcrm: permission denied for id (1228931141)
% 0.20/0.44  ipcrm: permission denied for id (1229029448)
% 0.20/0.44  ipcrm: permission denied for id (1229094986)
% 0.20/0.44  ipcrm: permission denied for id (1229127755)
% 0.20/0.44  ipcrm: permission denied for id (1229193293)
% 0.20/0.45  ipcrm: permission denied for id (1229324369)
% 0.20/0.45  ipcrm: permission denied for id (1229389907)
% 0.20/0.45  ipcrm: permission denied for id (1229520983)
% 0.20/0.46  ipcrm: permission denied for id (1229586521)
% 0.20/0.46  ipcrm: permission denied for id (1229619290)
% 0.20/0.46  ipcrm: permission denied for id (1229783135)
% 0.20/0.46  ipcrm: permission denied for id (1229815904)
% 0.20/0.47  ipcrm: permission denied for id (1229914211)
% 0.20/0.47  ipcrm: permission denied for id (1229946981)
% 0.20/0.47  ipcrm: permission denied for id (1229979750)
% 0.20/0.47  ipcrm: permission denied for id (1230012519)
% 0.20/0.47  ipcrm: permission denied for id (1230045288)
% 0.20/0.47  ipcrm: permission denied for id (1230078057)
% 0.20/0.48  ipcrm: permission denied for id (1230176364)
% 0.20/0.48  ipcrm: permission denied for id (1230241902)
% 0.20/0.48  ipcrm: permission denied for id (1230307440)
% 0.20/0.49  ipcrm: permission denied for id (1230405747)
% 0.20/0.49  ipcrm: permission denied for id (1230504054)
% 0.20/0.50  ipcrm: permission denied for id (1230667899)
% 0.20/0.50  ipcrm: permission denied for id (1230733437)
% 0.20/0.50  ipcrm: permission denied for id (1230798975)
% 0.70/0.59  % (31154)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.70/0.60  % (31160)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.70/0.61  % (31152)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.70/0.62  % (31151)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.70/0.62  % (31152)Refutation found. Thanks to Tanya!
% 0.70/0.62  % SZS status Theorem for theBenchmark
% 0.70/0.62  % SZS output start Proof for theBenchmark
% 0.70/0.62  fof(f282,plain,(
% 0.70/0.62    $false),
% 0.70/0.62    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f109,f114,f119,f124,f129,f146,f152,f160,f173,f181,f184,f194,f201,f208,f232,f246,f253,f266,f271,f275,f281])).
% 0.70/0.62  fof(f281,plain,(
% 0.70/0.62    ~spl3_1 | ~spl3_2 | ~spl3_17 | ~spl3_20 | ~spl3_26 | spl3_28),
% 0.70/0.62    inference(avatar_contradiction_clause,[],[f280])).
% 0.70/0.62  fof(f280,plain,(
% 0.70/0.62    $false | (~spl3_1 | ~spl3_2 | ~spl3_17 | ~spl3_20 | ~spl3_26 | spl3_28)),
% 0.70/0.62    inference(subsumption_resolution,[],[f279,f270])).
% 0.70/0.62  fof(f270,plain,(
% 0.70/0.62    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | spl3_28),
% 0.70/0.62    inference(avatar_component_clause,[],[f268])).
% 0.70/0.62  fof(f268,plain,(
% 0.70/0.62    spl3_28 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.70/0.62  fof(f279,plain,(
% 0.70/0.62    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_17 | ~spl3_20 | ~spl3_26)),
% 0.70/0.62    inference(forward_demodulation,[],[f278,f200])).
% 0.70/0.62  fof(f200,plain,(
% 0.70/0.62    k2_struct_0(sK1) = k9_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_20),
% 0.70/0.62    inference(avatar_component_clause,[],[f198])).
% 0.70/0.62  fof(f198,plain,(
% 0.70/0.62    spl3_20 <=> k2_struct_0(sK1) = k9_relat_1(sK2,k2_struct_0(sK0))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.70/0.62  fof(f278,plain,(
% 0.70/0.62    k9_relat_1(sK2,k2_struct_0(sK0)) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_17 | ~spl3_26)),
% 0.70/0.62    inference(forward_demodulation,[],[f259,f261])).
% 0.70/0.62  fof(f261,plain,(
% 0.70/0.62    ( ! [X1] : (k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1) = k9_relat_1(sK2,X1)) ) | (~spl3_1 | ~spl3_2 | ~spl3_17 | ~spl3_26)),
% 0.70/0.62    inference(forward_demodulation,[],[f255,f185])).
% 0.70/0.62  fof(f185,plain,(
% 0.70/0.62    ( ! [X7] : (k9_relat_1(sK2,X7) = k10_relat_1(k2_funct_1(sK2),X7)) ) | (~spl3_1 | ~spl3_2 | ~spl3_17)),
% 0.70/0.62    inference(subsumption_resolution,[],[f102,f179])).
% 0.70/0.62  fof(f179,plain,(
% 0.70/0.62    v1_relat_1(sK2) | ~spl3_17),
% 0.70/0.62    inference(avatar_component_clause,[],[f178])).
% 0.70/0.62  fof(f178,plain,(
% 0.70/0.62    spl3_17 <=> v1_relat_1(sK2)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.70/0.62  fof(f102,plain,(
% 0.70/0.62    ( ! [X7] : (~v1_relat_1(sK2) | k9_relat_1(sK2,X7) = k10_relat_1(k2_funct_1(sK2),X7)) ) | (~spl3_1 | ~spl3_2)),
% 0.70/0.62    inference(subsumption_resolution,[],[f97,f71])).
% 0.70/0.62  fof(f71,plain,(
% 0.70/0.62    v1_funct_1(sK2) | ~spl3_1),
% 0.70/0.62    inference(avatar_component_clause,[],[f69])).
% 0.70/0.62  fof(f69,plain,(
% 0.70/0.62    spl3_1 <=> v1_funct_1(sK2)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.70/0.62  fof(f97,plain,(
% 0.70/0.62    ( ! [X7] : (~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k9_relat_1(sK2,X7) = k10_relat_1(k2_funct_1(sK2),X7)) ) | ~spl3_2),
% 0.70/0.62    inference(resolution,[],[f76,f46])).
% 0.70/0.62  fof(f46,plain,(
% 0.70/0.62    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f21])).
% 0.70/0.62  fof(f21,plain,(
% 0.70/0.62    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.70/0.62    inference(flattening,[],[f20])).
% 0.70/0.62  fof(f20,plain,(
% 0.70/0.62    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.70/0.62    inference(ennf_transformation,[],[f2])).
% 0.70/0.62  fof(f2,axiom,(
% 0.70/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 0.70/0.62  fof(f76,plain,(
% 0.70/0.62    v2_funct_1(sK2) | ~spl3_2),
% 0.70/0.62    inference(avatar_component_clause,[],[f74])).
% 0.70/0.62  fof(f74,plain,(
% 0.70/0.62    spl3_2 <=> v2_funct_1(sK2)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.70/0.62  fof(f255,plain,(
% 0.70/0.62    ( ! [X1] : (k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1) = k10_relat_1(k2_funct_1(sK2),X1)) ) | ~spl3_26),
% 0.70/0.62    inference(resolution,[],[f252,f61])).
% 0.70/0.62  fof(f61,plain,(
% 0.70/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f32])).
% 0.70/0.62  fof(f32,plain,(
% 0.70/0.62    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.70/0.62    inference(ennf_transformation,[],[f6])).
% 0.70/0.62  fof(f6,axiom,(
% 0.70/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.70/0.62  fof(f252,plain,(
% 0.70/0.62    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_26),
% 0.70/0.62    inference(avatar_component_clause,[],[f250])).
% 0.70/0.62  fof(f250,plain,(
% 0.70/0.62    spl3_26 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.70/0.62  fof(f259,plain,(
% 0.70/0.62    k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k8_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),k2_struct_0(sK0)) | ~spl3_26),
% 0.70/0.62    inference(resolution,[],[f252,f50])).
% 0.70/0.62  fof(f50,plain,(
% 0.70/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f25])).
% 0.70/0.62  fof(f25,plain,(
% 0.70/0.62    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.70/0.62    inference(ennf_transformation,[],[f7])).
% 0.70/0.62  fof(f7,axiom,(
% 0.70/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.70/0.62  fof(f275,plain,(
% 0.70/0.62    ~spl3_16 | ~spl3_21 | ~spl3_26 | spl3_27),
% 0.70/0.62    inference(avatar_contradiction_clause,[],[f274])).
% 0.70/0.62  fof(f274,plain,(
% 0.70/0.62    $false | (~spl3_16 | ~spl3_21 | ~spl3_26 | spl3_27)),
% 0.70/0.62    inference(subsumption_resolution,[],[f273,f265])).
% 0.70/0.62  fof(f265,plain,(
% 0.70/0.62    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | spl3_27),
% 0.70/0.62    inference(avatar_component_clause,[],[f263])).
% 0.70/0.62  fof(f263,plain,(
% 0.70/0.62    spl3_27 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.70/0.62  fof(f273,plain,(
% 0.70/0.62    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_16 | ~spl3_21 | ~spl3_26)),
% 0.70/0.62    inference(forward_demodulation,[],[f272,f207])).
% 0.70/0.62  fof(f207,plain,(
% 0.70/0.62    k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) | ~spl3_21),
% 0.70/0.62    inference(avatar_component_clause,[],[f205])).
% 0.70/0.62  fof(f205,plain,(
% 0.70/0.62    spl3_21 <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.70/0.62  fof(f272,plain,(
% 0.70/0.62    k10_relat_1(sK2,k2_struct_0(sK1)) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_16 | ~spl3_26)),
% 0.70/0.62    inference(forward_demodulation,[],[f258,f260])).
% 0.70/0.62  fof(f260,plain,(
% 0.70/0.62    ( ! [X0] : (k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)) ) | (~spl3_16 | ~spl3_26)),
% 0.70/0.62    inference(forward_demodulation,[],[f254,f176])).
% 0.70/0.62  fof(f176,plain,(
% 0.70/0.62    ( ! [X6] : (k10_relat_1(sK2,X6) = k9_relat_1(k2_funct_1(sK2),X6)) ) | ~spl3_16),
% 0.70/0.62    inference(avatar_component_clause,[],[f175])).
% 0.70/0.62  fof(f175,plain,(
% 0.70/0.62    spl3_16 <=> ! [X6] : k10_relat_1(sK2,X6) = k9_relat_1(k2_funct_1(sK2),X6)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.70/0.62  fof(f254,plain,(
% 0.70/0.62    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)) ) | ~spl3_26),
% 0.70/0.62    inference(resolution,[],[f252,f62])).
% 0.70/0.62  fof(f62,plain,(
% 0.70/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f33])).
% 0.70/0.62  fof(f33,plain,(
% 0.70/0.62    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.70/0.62    inference(ennf_transformation,[],[f5])).
% 0.70/0.62  fof(f5,axiom,(
% 0.70/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.70/0.62  fof(f258,plain,(
% 0.70/0.62    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),k2_struct_0(sK1)) | ~spl3_26),
% 0.70/0.62    inference(resolution,[],[f252,f49])).
% 0.70/0.62  fof(f49,plain,(
% 0.70/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f25])).
% 0.70/0.62  fof(f271,plain,(
% 0.70/0.62    ~spl3_28 | spl3_14 | ~spl3_25),
% 0.70/0.62    inference(avatar_split_clause,[],[f248,f243,f166,f268])).
% 0.70/0.62  fof(f166,plain,(
% 0.70/0.62    spl3_14 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.70/0.62  fof(f243,plain,(
% 0.70/0.62    spl3_25 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.70/0.62  fof(f248,plain,(
% 0.70/0.62    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (spl3_14 | ~spl3_25)),
% 0.70/0.62    inference(superposition,[],[f168,f245])).
% 0.70/0.62  fof(f245,plain,(
% 0.70/0.62    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_25),
% 0.70/0.62    inference(avatar_component_clause,[],[f243])).
% 0.70/0.62  fof(f168,plain,(
% 0.70/0.62    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_14),
% 0.70/0.62    inference(avatar_component_clause,[],[f166])).
% 0.70/0.62  fof(f266,plain,(
% 0.70/0.62    ~spl3_27 | spl3_15 | ~spl3_25),
% 0.70/0.62    inference(avatar_split_clause,[],[f247,f243,f170,f263])).
% 0.70/0.62  fof(f170,plain,(
% 0.70/0.62    spl3_15 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.70/0.62  fof(f247,plain,(
% 0.70/0.62    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (spl3_15 | ~spl3_25)),
% 0.70/0.62    inference(superposition,[],[f172,f245])).
% 0.70/0.62  fof(f172,plain,(
% 0.70/0.62    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_15),
% 0.70/0.62    inference(avatar_component_clause,[],[f170])).
% 0.70/0.62  fof(f253,plain,(
% 0.70/0.62    spl3_26 | ~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_13),
% 0.70/0.62    inference(avatar_split_clause,[],[f241,f149,f143,f131,f74,f69,f250])).
% 0.70/0.62  fof(f131,plain,(
% 0.70/0.62    spl3_11 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.70/0.62  fof(f143,plain,(
% 0.70/0.62    spl3_12 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.70/0.62  fof(f149,plain,(
% 0.70/0.62    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.70/0.62  fof(f241,plain,(
% 0.70/0.62    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_13)),
% 0.70/0.62    inference(subsumption_resolution,[],[f240,f133])).
% 0.70/0.62  fof(f133,plain,(
% 0.70/0.62    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_11),
% 0.70/0.62    inference(avatar_component_clause,[],[f131])).
% 0.70/0.62  fof(f240,plain,(
% 0.70/0.62    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13)),
% 0.70/0.62    inference(subsumption_resolution,[],[f239,f145])).
% 0.70/0.62  fof(f145,plain,(
% 0.70/0.62    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_12),
% 0.70/0.62    inference(avatar_component_clause,[],[f143])).
% 0.70/0.62  fof(f239,plain,(
% 0.70/0.62    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.70/0.62    inference(resolution,[],[f100,f151])).
% 0.70/0.62  fof(f151,plain,(
% 0.70/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.70/0.62    inference(avatar_component_clause,[],[f149])).
% 0.70/0.62  fof(f100,plain,(
% 0.70/0.62    ( ! [X4,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(sK2,X4,X5) | k2_relset_1(X4,X5,sK2) != X5 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X4)))) ) | (~spl3_1 | ~spl3_2)),
% 0.70/0.62    inference(subsumption_resolution,[],[f95,f71])).
% 0.70/0.62  fof(f95,plain,(
% 0.70/0.62    ( ! [X4,X5] : (~v1_funct_2(sK2,X4,X5) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK2) | k2_relset_1(X4,X5,sK2) != X5 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X4)))) ) | ~spl3_2),
% 0.70/0.62    inference(resolution,[],[f76,f59])).
% 0.70/0.62  fof(f59,plain,(
% 0.70/0.62    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.70/0.62    inference(cnf_transformation,[],[f29])).
% 0.70/0.62  fof(f29,plain,(
% 0.70/0.62    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.70/0.62    inference(flattening,[],[f28])).
% 0.70/0.62  fof(f28,plain,(
% 0.70/0.62    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.70/0.62    inference(ennf_transformation,[],[f9])).
% 0.70/0.62  fof(f9,axiom,(
% 0.70/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.70/0.62  fof(f246,plain,(
% 0.70/0.62    spl3_25 | ~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_13),
% 0.70/0.62    inference(avatar_split_clause,[],[f238,f149,f143,f131,f74,f69,f243])).
% 0.70/0.62  fof(f238,plain,(
% 0.70/0.62    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_11 | ~spl3_12 | ~spl3_13)),
% 0.70/0.62    inference(subsumption_resolution,[],[f237,f133])).
% 0.70/0.62  fof(f237,plain,(
% 0.70/0.62    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13)),
% 0.70/0.62    inference(subsumption_resolution,[],[f236,f145])).
% 0.70/0.62  fof(f236,plain,(
% 0.70/0.62    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.70/0.62    inference(resolution,[],[f98,f151])).
% 0.70/0.62  fof(f98,plain,(
% 0.70/0.62    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) ) | (~spl3_1 | ~spl3_2)),
% 0.70/0.62    inference(subsumption_resolution,[],[f93,f71])).
% 0.70/0.62  fof(f93,plain,(
% 0.70/0.62    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) ) | ~spl3_2),
% 0.70/0.62    inference(resolution,[],[f76,f60])).
% 0.70/0.62  fof(f60,plain,(
% 0.70/0.62    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f31])).
% 0.70/0.62  fof(f31,plain,(
% 0.70/0.62    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.70/0.62    inference(flattening,[],[f30])).
% 0.70/0.62  fof(f30,plain,(
% 0.70/0.62    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.70/0.62    inference(ennf_transformation,[],[f12])).
% 0.70/0.62  fof(f12,axiom,(
% 0.70/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.70/0.62  fof(f232,plain,(
% 0.70/0.62    spl3_3 | ~spl3_4 | ~spl3_19),
% 0.70/0.62    inference(avatar_contradiction_clause,[],[f231])).
% 0.70/0.62  fof(f231,plain,(
% 0.70/0.62    $false | (spl3_3 | ~spl3_4 | ~spl3_19)),
% 0.70/0.62    inference(subsumption_resolution,[],[f230,f81])).
% 0.70/0.62  fof(f81,plain,(
% 0.70/0.62    ~v2_struct_0(sK1) | spl3_3),
% 0.70/0.62    inference(avatar_component_clause,[],[f79])).
% 0.70/0.62  fof(f79,plain,(
% 0.70/0.62    spl3_3 <=> v2_struct_0(sK1)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.70/0.62  fof(f230,plain,(
% 0.70/0.62    v2_struct_0(sK1) | (~spl3_4 | ~spl3_19)),
% 0.70/0.62    inference(subsumption_resolution,[],[f229,f86])).
% 0.70/0.62  fof(f86,plain,(
% 0.70/0.62    l1_struct_0(sK1) | ~spl3_4),
% 0.70/0.62    inference(avatar_component_clause,[],[f84])).
% 0.70/0.62  fof(f84,plain,(
% 0.70/0.62    spl3_4 <=> l1_struct_0(sK1)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.70/0.62  fof(f229,plain,(
% 0.70/0.62    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_19),
% 0.70/0.62    inference(subsumption_resolution,[],[f228,f43])).
% 0.70/0.62  fof(f43,plain,(
% 0.70/0.62    v1_xboole_0(k1_xboole_0)),
% 0.70/0.62    inference(cnf_transformation,[],[f1])).
% 0.70/0.62  fof(f1,axiom,(
% 0.70/0.62    v1_xboole_0(k1_xboole_0)),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.70/0.62  fof(f228,plain,(
% 0.70/0.62    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_19),
% 0.70/0.62    inference(superposition,[],[f45,f193])).
% 0.70/0.62  fof(f193,plain,(
% 0.70/0.62    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_19),
% 0.70/0.62    inference(avatar_component_clause,[],[f191])).
% 0.70/0.62  fof(f191,plain,(
% 0.70/0.62    spl3_19 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.70/0.62  fof(f45,plain,(
% 0.70/0.62    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f19])).
% 0.70/0.62  fof(f19,plain,(
% 0.70/0.62    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.70/0.62    inference(flattening,[],[f18])).
% 0.70/0.62  fof(f18,plain,(
% 0.70/0.62    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.70/0.62    inference(ennf_transformation,[],[f11])).
% 0.70/0.62  fof(f11,axiom,(
% 0.70/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.70/0.62  fof(f208,plain,(
% 0.70/0.62    spl3_21 | ~spl3_13 | ~spl3_18),
% 0.70/0.62    inference(avatar_split_clause,[],[f203,f187,f149,f205])).
% 0.70/0.62  fof(f187,plain,(
% 0.70/0.62    spl3_18 <=> k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.70/0.62  fof(f203,plain,(
% 0.70/0.62    k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) | (~spl3_13 | ~spl3_18)),
% 0.70/0.62    inference(forward_demodulation,[],[f202,f189])).
% 0.70/0.62  fof(f189,plain,(
% 0.70/0.62    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_18),
% 0.70/0.62    inference(avatar_component_clause,[],[f187])).
% 0.70/0.62  fof(f202,plain,(
% 0.70/0.62    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k10_relat_1(sK2,k2_struct_0(sK1)) | ~spl3_13),
% 0.70/0.62    inference(forward_demodulation,[],[f158,f154])).
% 0.70/0.62  fof(f154,plain,(
% 0.70/0.62    ( ! [X1] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1)) ) | ~spl3_13),
% 0.70/0.62    inference(resolution,[],[f151,f61])).
% 0.70/0.62  fof(f158,plain,(
% 0.70/0.62    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | ~spl3_13),
% 0.70/0.62    inference(resolution,[],[f151,f50])).
% 0.70/0.62  fof(f201,plain,(
% 0.70/0.62    spl3_20 | ~spl3_11 | ~spl3_13),
% 0.70/0.62    inference(avatar_split_clause,[],[f196,f149,f131,f198])).
% 0.70/0.62  fof(f196,plain,(
% 0.70/0.62    k2_struct_0(sK1) = k9_relat_1(sK2,k2_struct_0(sK0)) | (~spl3_11 | ~spl3_13)),
% 0.70/0.62    inference(forward_demodulation,[],[f195,f133])).
% 0.70/0.62  fof(f195,plain,(
% 0.70/0.62    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k9_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.70/0.62    inference(forward_demodulation,[],[f157,f153])).
% 0.70/0.62  fof(f153,plain,(
% 0.70/0.62    ( ! [X0] : (k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl3_13),
% 0.70/0.62    inference(resolution,[],[f151,f62])).
% 0.70/0.62  fof(f157,plain,(
% 0.70/0.62    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.70/0.62    inference(resolution,[],[f151,f49])).
% 0.70/0.62  fof(f194,plain,(
% 0.70/0.62    spl3_18 | spl3_19 | ~spl3_12 | ~spl3_13),
% 0.70/0.62    inference(avatar_split_clause,[],[f159,f149,f143,f191,f187])).
% 0.70/0.62  fof(f159,plain,(
% 0.70/0.62    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_12 | ~spl3_13)),
% 0.70/0.62    inference(subsumption_resolution,[],[f156,f145])).
% 0.70/0.62  fof(f156,plain,(
% 0.70/0.62    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_13),
% 0.70/0.62    inference(resolution,[],[f151,f56])).
% 0.70/0.62  fof(f56,plain,(
% 0.70/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f27])).
% 0.70/0.62  fof(f27,plain,(
% 0.70/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.70/0.62    inference(flattening,[],[f26])).
% 0.70/0.62  fof(f26,plain,(
% 0.70/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.70/0.62    inference(ennf_transformation,[],[f8])).
% 0.70/0.62  fof(f8,axiom,(
% 0.70/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.70/0.62  fof(f184,plain,(
% 0.70/0.62    ~spl3_13 | spl3_17),
% 0.70/0.62    inference(avatar_contradiction_clause,[],[f183])).
% 0.70/0.62  fof(f183,plain,(
% 0.70/0.62    $false | (~spl3_13 | spl3_17)),
% 0.70/0.62    inference(resolution,[],[f182,f151])).
% 0.70/0.62  fof(f182,plain,(
% 0.70/0.62    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_17),
% 0.70/0.62    inference(resolution,[],[f180,f48])).
% 0.70/0.62  fof(f48,plain,(
% 0.70/0.62    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.70/0.62    inference(cnf_transformation,[],[f24])).
% 0.70/0.62  fof(f24,plain,(
% 0.70/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.70/0.62    inference(ennf_transformation,[],[f4])).
% 0.70/0.62  fof(f4,axiom,(
% 0.70/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.70/0.62  fof(f180,plain,(
% 0.70/0.62    ~v1_relat_1(sK2) | spl3_17),
% 0.70/0.62    inference(avatar_component_clause,[],[f178])).
% 0.70/0.62  fof(f181,plain,(
% 0.70/0.62    spl3_16 | ~spl3_17 | ~spl3_1 | ~spl3_2),
% 0.70/0.62    inference(avatar_split_clause,[],[f101,f74,f69,f178,f175])).
% 0.70/0.62  fof(f101,plain,(
% 0.70/0.62    ( ! [X6] : (~v1_relat_1(sK2) | k10_relat_1(sK2,X6) = k9_relat_1(k2_funct_1(sK2),X6)) ) | (~spl3_1 | ~spl3_2)),
% 0.70/0.62    inference(subsumption_resolution,[],[f96,f71])).
% 0.70/0.62  fof(f96,plain,(
% 0.70/0.62    ( ! [X6] : (~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k10_relat_1(sK2,X6) = k9_relat_1(k2_funct_1(sK2),X6)) ) | ~spl3_2),
% 0.70/0.62    inference(resolution,[],[f76,f47])).
% 0.70/0.62  fof(f47,plain,(
% 0.70/0.62    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f23])).
% 0.70/0.62  fof(f23,plain,(
% 0.70/0.62    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.70/0.62    inference(flattening,[],[f22])).
% 0.70/0.62  fof(f22,plain,(
% 0.70/0.62    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.70/0.62    inference(ennf_transformation,[],[f3])).
% 0.70/0.62  fof(f3,axiom,(
% 0.70/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.70/0.62  fof(f173,plain,(
% 0.70/0.62    ~spl3_14 | ~spl3_15 | ~spl3_7 | ~spl3_9),
% 0.70/0.62    inference(avatar_split_clause,[],[f164,f121,f111,f170,f166])).
% 0.70/0.62  fof(f111,plain,(
% 0.70/0.62    spl3_7 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.70/0.62  fof(f121,plain,(
% 0.70/0.62    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.70/0.62  fof(f164,plain,(
% 0.70/0.62    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.70/0.62    inference(forward_demodulation,[],[f163,f123])).
% 0.70/0.62  fof(f123,plain,(
% 0.70/0.62    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.70/0.62    inference(avatar_component_clause,[],[f121])).
% 0.70/0.62  fof(f163,plain,(
% 0.70/0.62    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.70/0.62    inference(forward_demodulation,[],[f162,f113])).
% 0.70/0.62  fof(f113,plain,(
% 0.70/0.62    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_7),
% 0.70/0.62    inference(avatar_component_clause,[],[f111])).
% 0.70/0.62  fof(f162,plain,(
% 0.70/0.62    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.70/0.62    inference(forward_demodulation,[],[f161,f123])).
% 0.70/0.62  fof(f161,plain,(
% 0.70/0.62    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl3_7),
% 0.70/0.62    inference(forward_demodulation,[],[f34,f113])).
% 0.70/0.62  fof(f34,plain,(
% 0.70/0.62    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.70/0.62    inference(cnf_transformation,[],[f16])).
% 0.70/0.62  fof(f16,plain,(
% 0.70/0.62    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.70/0.62    inference(flattening,[],[f15])).
% 0.70/0.62  fof(f15,plain,(
% 0.70/0.62    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.70/0.62    inference(ennf_transformation,[],[f14])).
% 0.70/0.62  fof(f14,negated_conjecture,(
% 0.70/0.62    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.70/0.62    inference(negated_conjecture,[],[f13])).
% 0.70/0.62  fof(f13,conjecture,(
% 0.70/0.62    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.70/0.62  fof(f160,plain,(
% 0.70/0.62    spl3_11 | ~spl3_7 | ~spl3_9 | ~spl3_10),
% 0.70/0.62    inference(avatar_split_clause,[],[f141,f126,f121,f111,f131])).
% 0.70/0.62  fof(f126,plain,(
% 0.70/0.62    spl3_10 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.70/0.62  fof(f141,plain,(
% 0.70/0.62    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10)),
% 0.70/0.62    inference(forward_demodulation,[],[f136,f123])).
% 0.70/0.62  fof(f136,plain,(
% 0.70/0.62    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_10)),
% 0.70/0.62    inference(forward_demodulation,[],[f128,f113])).
% 0.70/0.62  fof(f128,plain,(
% 0.70/0.62    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_10),
% 0.70/0.62    inference(avatar_component_clause,[],[f126])).
% 0.70/0.62  fof(f152,plain,(
% 0.70/0.62    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.70/0.62    inference(avatar_split_clause,[],[f139,f121,f116,f111,f149])).
% 0.70/0.62  fof(f116,plain,(
% 0.70/0.62    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.70/0.62  fof(f139,plain,(
% 0.70/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.70/0.62    inference(forward_demodulation,[],[f135,f123])).
% 0.70/0.62  fof(f135,plain,(
% 0.70/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 0.70/0.62    inference(forward_demodulation,[],[f118,f113])).
% 0.70/0.62  fof(f118,plain,(
% 0.70/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.70/0.62    inference(avatar_component_clause,[],[f116])).
% 0.70/0.62  fof(f146,plain,(
% 0.70/0.62    spl3_12 | ~spl3_6 | ~spl3_7 | ~spl3_9),
% 0.70/0.62    inference(avatar_split_clause,[],[f138,f121,f111,f106,f143])).
% 0.70/0.62  fof(f106,plain,(
% 0.70/0.62    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.70/0.62  fof(f138,plain,(
% 0.70/0.62    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_7 | ~spl3_9)),
% 0.70/0.62    inference(forward_demodulation,[],[f137,f113])).
% 0.70/0.62  fof(f137,plain,(
% 0.70/0.62    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl3_6 | ~spl3_9)),
% 0.70/0.62    inference(superposition,[],[f108,f123])).
% 0.70/0.62  fof(f108,plain,(
% 0.70/0.62    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.70/0.62    inference(avatar_component_clause,[],[f106])).
% 0.70/0.62  fof(f129,plain,(
% 0.70/0.62    spl3_10),
% 0.70/0.62    inference(avatar_split_clause,[],[f38,f126])).
% 0.70/0.62  fof(f38,plain,(
% 0.70/0.62    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.70/0.62    inference(cnf_transformation,[],[f16])).
% 0.70/0.62  fof(f124,plain,(
% 0.70/0.62    spl3_9 | ~spl3_5),
% 0.70/0.62    inference(avatar_split_clause,[],[f104,f89,f121])).
% 0.70/0.62  fof(f89,plain,(
% 0.70/0.62    spl3_5 <=> l1_struct_0(sK0)),
% 0.70/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.70/0.62  fof(f104,plain,(
% 0.70/0.62    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.70/0.62    inference(resolution,[],[f91,f44])).
% 0.70/0.62  fof(f44,plain,(
% 0.70/0.62    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.70/0.62    inference(cnf_transformation,[],[f17])).
% 0.70/0.62  fof(f17,plain,(
% 0.70/0.62    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.70/0.62    inference(ennf_transformation,[],[f10])).
% 0.70/0.62  fof(f10,axiom,(
% 0.70/0.62    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.70/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.70/0.62  fof(f91,plain,(
% 0.70/0.62    l1_struct_0(sK0) | ~spl3_5),
% 0.70/0.62    inference(avatar_component_clause,[],[f89])).
% 0.70/0.62  fof(f119,plain,(
% 0.70/0.62    spl3_8),
% 0.70/0.62    inference(avatar_split_clause,[],[f37,f116])).
% 0.70/0.62  fof(f37,plain,(
% 0.70/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.70/0.62    inference(cnf_transformation,[],[f16])).
% 0.70/0.62  fof(f114,plain,(
% 0.70/0.62    spl3_7 | ~spl3_4),
% 0.70/0.62    inference(avatar_split_clause,[],[f103,f84,f111])).
% 0.70/0.62  fof(f103,plain,(
% 0.70/0.62    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_4),
% 0.70/0.62    inference(resolution,[],[f86,f44])).
% 0.70/0.62  fof(f109,plain,(
% 0.70/0.62    spl3_6),
% 0.70/0.62    inference(avatar_split_clause,[],[f36,f106])).
% 0.70/0.62  fof(f36,plain,(
% 0.70/0.62    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.70/0.62    inference(cnf_transformation,[],[f16])).
% 0.70/0.62  fof(f92,plain,(
% 0.70/0.62    spl3_5),
% 0.70/0.62    inference(avatar_split_clause,[],[f42,f89])).
% 0.70/0.62  fof(f42,plain,(
% 0.70/0.62    l1_struct_0(sK0)),
% 0.70/0.62    inference(cnf_transformation,[],[f16])).
% 0.70/0.62  fof(f87,plain,(
% 0.70/0.62    spl3_4),
% 0.70/0.62    inference(avatar_split_clause,[],[f41,f84])).
% 0.70/0.62  fof(f41,plain,(
% 0.70/0.62    l1_struct_0(sK1)),
% 0.70/0.62    inference(cnf_transformation,[],[f16])).
% 0.70/0.62  fof(f82,plain,(
% 0.70/0.62    ~spl3_3),
% 0.70/0.62    inference(avatar_split_clause,[],[f40,f79])).
% 0.70/0.62  fof(f40,plain,(
% 0.70/0.62    ~v2_struct_0(sK1)),
% 0.70/0.62    inference(cnf_transformation,[],[f16])).
% 0.70/0.62  fof(f77,plain,(
% 0.70/0.62    spl3_2),
% 0.70/0.62    inference(avatar_split_clause,[],[f39,f74])).
% 0.70/0.62  fof(f39,plain,(
% 0.70/0.62    v2_funct_1(sK2)),
% 0.70/0.62    inference(cnf_transformation,[],[f16])).
% 0.70/0.62  fof(f72,plain,(
% 0.70/0.62    spl3_1),
% 0.70/0.62    inference(avatar_split_clause,[],[f35,f69])).
% 0.70/0.62  fof(f35,plain,(
% 0.70/0.62    v1_funct_1(sK2)),
% 0.70/0.62    inference(cnf_transformation,[],[f16])).
% 0.70/0.62  % SZS output end Proof for theBenchmark
% 0.70/0.62  % (31152)------------------------------
% 0.70/0.62  % (31152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.70/0.62  % (31152)Termination reason: Refutation
% 0.70/0.62  
% 0.70/0.62  % (31152)Memory used [KB]: 10746
% 0.70/0.62  % (31152)Time elapsed: 0.063 s
% 0.70/0.62  % (31152)------------------------------
% 0.70/0.62  % (31152)------------------------------
% 0.70/0.62  % (30958)Success in time 0.27 s
%------------------------------------------------------------------------------
