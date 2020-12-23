%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 227 expanded)
%              Number of leaves         :   28 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  346 (1044 expanded)
%              Number of equality atoms :   44 ( 153 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f64,f69,f74,f102,f108,f134,f145,f153,f163,f182,f187,f199,f213,f220,f225])).

fof(f225,plain,
    ( ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | spl3_25 ),
    inference(subsumption_resolution,[],[f223,f81])).

fof(f81,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f223,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_6
    | spl3_25 ),
    inference(subsumption_resolution,[],[f222,f63])).

fof(f63,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f222,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | spl3_25 ),
    inference(subsumption_resolution,[],[f221,f43])).

fof(f43,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f221,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_25 ),
    inference(resolution,[],[f219,f34])).

fof(f34,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f219,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl3_25
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f220,plain,
    ( ~ spl3_25
    | ~ spl3_13
    | spl3_16
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f215,f206,f131,f105,f217])).

fof(f105,plain,
    ( spl3_13
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f131,plain,
    ( spl3_16
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f206,plain,
    ( spl3_24
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f215,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_13
    | spl3_16
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f214,f208])).

fof(f208,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f206])).

fof(f214,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_13
    | spl3_16 ),
    inference(forward_demodulation,[],[f133,f107])).

fof(f107,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f133,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f213,plain,
    ( ~ spl3_21
    | ~ spl3_20
    | spl3_24
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f212,f196,f61,f41,f206,f179,f184])).

fof(f184,plain,
    ( spl3_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f179,plain,
    ( spl3_20
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f196,plain,
    ( spl3_23
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f212,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f211,f63])).

fof(f211,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f210,f43])).

fof(f210,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_23 ),
    inference(resolution,[],[f198,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f198,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f196])).

fof(f199,plain,
    ( spl3_23
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f194,f105,f99,f56,f196])).

fof(f56,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f99,plain,
    ( spl3_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f194,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f177,f101])).

fof(f101,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f177,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(superposition,[],[f58,f107])).

fof(f58,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f187,plain,
    ( spl3_21
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f175,f142,f105,f184])).

fof(f142,plain,
    ( spl3_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f175,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(superposition,[],[f144,f107])).

fof(f144,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f182,plain,
    ( spl3_20
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f174,f160,f105,f179])).

fof(f160,plain,
    ( spl3_19
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f174,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(superposition,[],[f162,f107])).

fof(f162,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f163,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f158,f99,f46,f160])).

fof(f46,plain,
    ( spl3_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f158,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f48,f101])).

fof(f48,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f153,plain,
    ( spl3_9
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f152,f142,f80])).

fof(f152,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f147,f31])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f147,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_18 ),
    inference(resolution,[],[f144,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f145,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f140,f99,f51,f142])).

fof(f51,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f53,f101])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f134,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f128,f99,f36,f131])).

fof(f36,plain,
    ( spl3_1
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f128,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_1
    | ~ spl3_12 ),
    inference(superposition,[],[f38,f101])).

fof(f38,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f108,plain,
    ( spl3_13
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f103,f71,f105])).

fof(f71,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f103,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f73,f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f73,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f102,plain,
    ( spl3_12
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f97,f66,f99])).

fof(f66,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f97,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f68,f29])).

fof(f68,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f74,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f20,f71])).

fof(f20,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(f69,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f66])).

fof(f21,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f61])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f51])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f46])).

fof(f25,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f41])).

fof(f26,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f36])).

fof(f27,plain,(
    ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (14139)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.49  % (14146)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (14143)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (14146)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f59,f64,f69,f74,f102,f108,f134,f145,f153,f163,f182,f187,f199,f213,f220,f225])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ~spl3_2 | ~spl3_6 | ~spl3_9 | spl3_25),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    $false | (~spl3_2 | ~spl3_6 | ~spl3_9 | spl3_25)),
% 0.22/0.50    inference(subsumption_resolution,[],[f223,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl3_9 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_6 | spl3_25)),
% 0.22/0.50    inference(subsumption_resolution,[],[f222,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    v1_funct_1(sK2) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl3_6 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_2 | spl3_25)),
% 0.22/0.50    inference(subsumption_resolution,[],[f221,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_25),
% 0.22/0.50    inference(resolution,[],[f219,f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    ~v2_funct_1(k2_funct_1(sK2)) | spl3_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    spl3_25 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    ~spl3_25 | ~spl3_13 | spl3_16 | ~spl3_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f215,f206,f131,f105,f217])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl3_13 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl3_16 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    spl3_24 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_13 | spl3_16 | ~spl3_24)),
% 0.22/0.50    inference(forward_demodulation,[],[f214,f208])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f206])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_13 | spl3_16)),
% 0.22/0.50    inference(forward_demodulation,[],[f133,f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f105])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f131])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ~spl3_21 | ~spl3_20 | spl3_24 | ~spl3_2 | ~spl3_6 | ~spl3_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f212,f196,f61,f41,f206,f179,f184])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    spl3_21 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    spl3_20 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    spl3_23 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_2 | ~spl3_6 | ~spl3_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f211,f63])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_23)),
% 0.22/0.50    inference(subsumption_resolution,[],[f210,f43])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~spl3_23),
% 0.22/0.50    inference(resolution,[],[f198,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f196])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    spl3_23 | ~spl3_5 | ~spl3_12 | ~spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f194,f105,f99,f56,f196])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_12 | ~spl3_13)),
% 0.22/0.50    inference(forward_demodulation,[],[f177,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl3_5 | ~spl3_13)),
% 0.22/0.50    inference(superposition,[],[f58,f107])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    spl3_21 | ~spl3_13 | ~spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f175,f142,f105,f184])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl3_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_13 | ~spl3_18)),
% 0.22/0.50    inference(superposition,[],[f144,f107])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f142])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    spl3_20 | ~spl3_13 | ~spl3_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f174,f160,f105,f179])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl3_19 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_13 | ~spl3_19)),
% 0.22/0.50    inference(superposition,[],[f162,f107])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f160])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl3_19 | ~spl3_3 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f158,f99,f46,f160])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    spl3_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_12)),
% 0.22/0.50    inference(forward_demodulation,[],[f48,f101])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f46])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl3_9 | ~spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f152,f142,f80])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~spl3_18),
% 0.22/0.50    inference(subsumption_resolution,[],[f147,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))) | ~spl3_18),
% 0.22/0.50    inference(resolution,[],[f144,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    spl3_18 | ~spl3_4 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f140,f99,f51,f142])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_12)),
% 0.22/0.50    inference(forward_demodulation,[],[f53,f101])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f51])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ~spl3_16 | spl3_1 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f128,f99,f36,f131])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    spl3_1 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl3_1 | ~spl3_12)),
% 0.22/0.50    inference(superposition,[],[f38,f101])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f36])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl3_13 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f103,f71,f105])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl3_8 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.22/0.50    inference(resolution,[],[f73,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f71])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl3_12 | ~spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f97,f66,f99])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl3_7 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.22/0.50    inference(resolution,[],[f68,f29])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f20,f71])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ((~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f18,f17,f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f6])).
% 0.22/0.50  fof(f6,conjecture,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f21,f66])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    l1_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f61])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f56])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f51])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f46])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f41])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    v2_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ~spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f36])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (14146)------------------------------
% 0.22/0.50  % (14146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14146)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (14146)Memory used [KB]: 6268
% 0.22/0.50  % (14146)Time elapsed: 0.086 s
% 0.22/0.50  % (14146)------------------------------
% 0.22/0.50  % (14146)------------------------------
% 0.22/0.50  % (14154)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % (14138)Success in time 0.142 s
%------------------------------------------------------------------------------
