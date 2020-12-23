%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 184 expanded)
%              Number of leaves         :   30 (  90 expanded)
%              Depth                    :    6
%              Number of atoms          :  281 ( 463 expanded)
%              Number of equality atoms :   69 ( 120 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f46,f50,f54,f58,f62,f66,f70,f74,f89,f95,f107,f112,f118,f124,f130,f137,f144,f165,f169,f179])).

fof(f179,plain,
    ( spl3_2
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl3_2
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f177,f117])).

fof(f117,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_19
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f177,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k1_relat_1(sK2)
    | spl3_2
    | ~ spl3_21
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f176,f164])).

fof(f164,plain,
    ( k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl3_26
  <=> k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f176,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | spl3_2
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f36,f129])).

fof(f129,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_21
  <=> k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f36,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_2
  <=> k1_relset_1(sK0,sK1,sK2) = k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f169,plain,
    ( spl3_22
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f166,f141,f104,f60,f134])).

fof(f134,plain,
    ( spl3_22
  <=> k2_relat_1(sK2) = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f60,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f104,plain,
    ( spl3_17
  <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f141,plain,
    ( spl3_23
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f166,plain,
    ( k2_relat_1(sK2) = k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f148,f106])).

fof(f106,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f104])).

fof(f148,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(resolution,[],[f143,f61])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f143,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f141])).

fof(f165,plain,
    ( spl3_26
    | ~ spl3_9
    | ~ spl3_18
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f160,f141,f109,f64,f162])).

fof(f64,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f109,plain,
    ( spl3_18
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f160,plain,
    ( k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_18
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f147,f111])).

fof(f111,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f109])).

fof(f147,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(resolution,[],[f143,f65])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f144,plain,
    ( spl3_23
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f139,f127,f72,f39,f141])).

fof(f39,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f139,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f138,f129])).

fof(f138,plain,
    ( m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f73,f41])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f137,plain,
    ( ~ spl3_22
    | spl3_1
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f132,f127,f121,f30,f134])).

fof(f30,plain,
    ( spl3_1
  <=> k2_relset_1(sK0,sK1,sK2) = k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f121,plain,
    ( spl3_20
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f132,plain,
    ( k2_relat_1(sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | spl3_1
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f131,f123])).

fof(f123,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f121])).

fof(f131,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2))
    | spl3_1
    | ~ spl3_21 ),
    inference(superposition,[],[f32,f129])).

fof(f32,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f130,plain,
    ( spl3_21
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f125,f68,f39,f127])).

fof(f68,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f125,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f69,f41])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f124,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f119,f64,f39,f121])).

fof(f119,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f65,f41])).

fof(f118,plain,
    ( spl3_19
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f113,f60,f39,f115])).

fof(f113,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f61,f41])).

fof(f112,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f98,f92,f44,f109])).

fof(f44,plain,
    ( spl3_4
  <=> ! [X0] :
        ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f92,plain,
    ( spl3_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f98,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(resolution,[],[f94,f45])).

fof(f45,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f94,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f92])).

fof(f107,plain,
    ( spl3_17
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f97,f92,f48,f104])).

fof(f48,plain,
    ( spl3_5
  <=> ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f97,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(resolution,[],[f94,f49])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f95,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f90,f87,f39,f92])).

fof(f87,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f90,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(resolution,[],[f88,f41])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( spl3_14
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f85,f56,f52,f87])).

fof(f52,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f56,plain,
    ( spl3_7
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f53,f57])).

fof(f57,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f74,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f28,f72])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f70,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f27,f68])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f66,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f58,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f54,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
      | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
        | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

fof(f37,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f34,f30])).

fof(f20,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.39  % (25335)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (25333)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (25333)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f182,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f37,f42,f46,f50,f54,f58,f62,f66,f70,f74,f89,f95,f107,f112,f118,f124,f130,f137,f144,f165,f169,f179])).
% 0.21/0.41  fof(f179,plain,(
% 0.21/0.41    spl3_2 | ~spl3_19 | ~spl3_21 | ~spl3_26),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.41  fof(f178,plain,(
% 0.21/0.41    $false | (spl3_2 | ~spl3_19 | ~spl3_21 | ~spl3_26)),
% 0.21/0.41    inference(subsumption_resolution,[],[f177,f117])).
% 0.21/0.41  fof(f117,plain,(
% 0.21/0.41    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl3_19),
% 0.21/0.41    inference(avatar_component_clause,[],[f115])).
% 0.21/0.41  fof(f115,plain,(
% 0.21/0.41    spl3_19 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.41  fof(f177,plain,(
% 0.21/0.41    k1_relset_1(sK0,sK1,sK2) != k1_relat_1(sK2) | (spl3_2 | ~spl3_21 | ~spl3_26)),
% 0.21/0.41    inference(forward_demodulation,[],[f176,f164])).
% 0.21/0.41  fof(f164,plain,(
% 0.21/0.41    k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | ~spl3_26),
% 0.21/0.41    inference(avatar_component_clause,[],[f162])).
% 0.21/0.41  fof(f162,plain,(
% 0.21/0.41    spl3_26 <=> k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.41  fof(f176,plain,(
% 0.21/0.41    k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | (spl3_2 | ~spl3_21)),
% 0.21/0.41    inference(forward_demodulation,[],[f36,f129])).
% 0.21/0.41  fof(f129,plain,(
% 0.21/0.41    k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) | ~spl3_21),
% 0.21/0.41    inference(avatar_component_clause,[],[f127])).
% 0.21/0.41  fof(f127,plain,(
% 0.21/0.41    spl3_21 <=> k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | spl3_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f34])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    spl3_2 <=> k1_relset_1(sK0,sK1,sK2) = k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.41  fof(f169,plain,(
% 0.21/0.41    spl3_22 | ~spl3_8 | ~spl3_17 | ~spl3_23),
% 0.21/0.41    inference(avatar_split_clause,[],[f166,f141,f104,f60,f134])).
% 0.21/0.41  fof(f134,plain,(
% 0.21/0.41    spl3_22 <=> k2_relat_1(sK2) = k1_relset_1(sK1,sK0,k4_relat_1(sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    spl3_8 <=> ! [X1,X0,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.41  fof(f104,plain,(
% 0.21/0.41    spl3_17 <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.41  fof(f141,plain,(
% 0.21/0.41    spl3_23 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.41  fof(f166,plain,(
% 0.21/0.41    k2_relat_1(sK2) = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | (~spl3_8 | ~spl3_17 | ~spl3_23)),
% 0.21/0.41    inference(forward_demodulation,[],[f148,f106])).
% 0.21/0.41  fof(f106,plain,(
% 0.21/0.41    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | ~spl3_17),
% 0.21/0.41    inference(avatar_component_clause,[],[f104])).
% 0.21/0.41  fof(f148,plain,(
% 0.21/0.41    k1_relat_1(k4_relat_1(sK2)) = k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | (~spl3_8 | ~spl3_23)),
% 0.21/0.41    inference(resolution,[],[f143,f61])).
% 0.21/0.41  fof(f61,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) ) | ~spl3_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f60])).
% 0.21/0.41  fof(f143,plain,(
% 0.21/0.41    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl3_23),
% 0.21/0.41    inference(avatar_component_clause,[],[f141])).
% 0.21/0.41  fof(f165,plain,(
% 0.21/0.41    spl3_26 | ~spl3_9 | ~spl3_18 | ~spl3_23),
% 0.21/0.41    inference(avatar_split_clause,[],[f160,f141,f109,f64,f162])).
% 0.21/0.41  fof(f64,plain,(
% 0.21/0.41    spl3_9 <=> ! [X1,X0,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.41  fof(f109,plain,(
% 0.21/0.41    spl3_18 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.41  fof(f160,plain,(
% 0.21/0.41    k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | (~spl3_9 | ~spl3_18 | ~spl3_23)),
% 0.21/0.41    inference(forward_demodulation,[],[f147,f111])).
% 0.21/0.41  fof(f111,plain,(
% 0.21/0.41    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl3_18),
% 0.21/0.41    inference(avatar_component_clause,[],[f109])).
% 0.21/0.41  fof(f147,plain,(
% 0.21/0.41    k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(sK1,sK0,k4_relat_1(sK2)) | (~spl3_9 | ~spl3_23)),
% 0.21/0.41    inference(resolution,[],[f143,f65])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl3_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f64])).
% 0.21/0.41  fof(f144,plain,(
% 0.21/0.41    spl3_23 | ~spl3_3 | ~spl3_11 | ~spl3_21),
% 0.21/0.41    inference(avatar_split_clause,[],[f139,f127,f72,f39,f141])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    spl3_11 <=> ! [X1,X0,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.41  fof(f139,plain,(
% 0.21/0.41    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_3 | ~spl3_11 | ~spl3_21)),
% 0.21/0.41    inference(forward_demodulation,[],[f138,f129])).
% 0.21/0.41  fof(f138,plain,(
% 0.21/0.41    m1_subset_1(k3_relset_1(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_3 | ~spl3_11)),
% 0.21/0.41    inference(resolution,[],[f73,f41])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f39])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f72])).
% 0.21/0.41  fof(f137,plain,(
% 0.21/0.41    ~spl3_22 | spl3_1 | ~spl3_20 | ~spl3_21),
% 0.21/0.41    inference(avatar_split_clause,[],[f132,f127,f121,f30,f134])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    spl3_1 <=> k2_relset_1(sK0,sK1,sK2) = k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.41  fof(f121,plain,(
% 0.21/0.41    spl3_20 <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.41  fof(f132,plain,(
% 0.21/0.41    k2_relat_1(sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | (spl3_1 | ~spl3_20 | ~spl3_21)),
% 0.21/0.41    inference(forward_demodulation,[],[f131,f123])).
% 0.21/0.41  fof(f123,plain,(
% 0.21/0.41    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_20),
% 0.21/0.41    inference(avatar_component_clause,[],[f121])).
% 0.21/0.41  fof(f131,plain,(
% 0.21/0.41    k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k4_relat_1(sK2)) | (spl3_1 | ~spl3_21)),
% 0.21/0.41    inference(superposition,[],[f32,f129])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | spl3_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f30])).
% 0.21/0.41  fof(f130,plain,(
% 0.21/0.41    spl3_21 | ~spl3_3 | ~spl3_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f125,f68,f39,f127])).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    spl3_10 <=> ! [X1,X0,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.41  fof(f125,plain,(
% 0.21/0.41    k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) | (~spl3_3 | ~spl3_10)),
% 0.21/0.41    inference(resolution,[],[f69,f41])).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) ) | ~spl3_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f68])).
% 0.21/0.41  fof(f124,plain,(
% 0.21/0.41    spl3_20 | ~spl3_3 | ~spl3_9),
% 0.21/0.41    inference(avatar_split_clause,[],[f119,f64,f39,f121])).
% 0.21/0.41  fof(f119,plain,(
% 0.21/0.41    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | (~spl3_3 | ~spl3_9)),
% 0.21/0.41    inference(resolution,[],[f65,f41])).
% 0.21/0.41  fof(f118,plain,(
% 0.21/0.41    spl3_19 | ~spl3_3 | ~spl3_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f113,f60,f39,f115])).
% 0.21/0.41  fof(f113,plain,(
% 0.21/0.41    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | (~spl3_3 | ~spl3_8)),
% 0.21/0.41    inference(resolution,[],[f61,f41])).
% 0.21/0.41  fof(f112,plain,(
% 0.21/0.41    spl3_18 | ~spl3_4 | ~spl3_15),
% 0.21/0.41    inference(avatar_split_clause,[],[f98,f92,f44,f109])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    spl3_4 <=> ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.41  fof(f92,plain,(
% 0.21/0.41    spl3_15 <=> v1_relat_1(sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.41  fof(f98,plain,(
% 0.21/0.41    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | (~spl3_4 | ~spl3_15)),
% 0.21/0.41    inference(resolution,[],[f94,f45])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) ) | ~spl3_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f44])).
% 0.21/0.41  fof(f94,plain,(
% 0.21/0.41    v1_relat_1(sK2) | ~spl3_15),
% 0.21/0.41    inference(avatar_component_clause,[],[f92])).
% 0.21/0.41  fof(f107,plain,(
% 0.21/0.41    spl3_17 | ~spl3_5 | ~spl3_15),
% 0.21/0.41    inference(avatar_split_clause,[],[f97,f92,f48,f104])).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl3_5 <=> ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | (~spl3_5 | ~spl3_15)),
% 0.21/0.41    inference(resolution,[],[f94,f49])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) ) | ~spl3_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f48])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    spl3_15 | ~spl3_3 | ~spl3_14),
% 0.21/0.41    inference(avatar_split_clause,[],[f90,f87,f39,f92])).
% 0.21/0.41  fof(f87,plain,(
% 0.21/0.41    spl3_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.41  fof(f90,plain,(
% 0.21/0.41    v1_relat_1(sK2) | (~spl3_3 | ~spl3_14)),
% 0.21/0.41    inference(resolution,[],[f88,f41])).
% 0.21/0.41  fof(f88,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | ~spl3_14),
% 0.21/0.41    inference(avatar_component_clause,[],[f87])).
% 0.21/0.41  fof(f89,plain,(
% 0.21/0.41    spl3_14 | ~spl3_6 | ~spl3_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f85,f56,f52,f87])).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    spl3_6 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.41  fof(f56,plain,(
% 0.21/0.41    spl3_7 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.41  fof(f85,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.41    inference(resolution,[],[f53,f57])).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl3_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f56])).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) ) | ~spl3_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f52])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    spl3_11),
% 0.21/0.41    inference(avatar_split_clause,[],[f28,f72])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    spl3_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f27,f68])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.21/0.41  fof(f66,plain,(
% 0.21/0.41    spl3_9),
% 0.21/0.41    inference(avatar_split_clause,[],[f26,f64])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    spl3_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f25,f60])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    spl3_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f24,f56])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    spl3_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f23,f52])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    spl3_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f48])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    spl3_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    spl3_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f19,f39])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    (k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) | k2_relset_1(X0,X1,X2) != k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.41    inference(ennf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 0.21/0.41    inference(negated_conjecture,[],[f8])).
% 0.21/0.41  fof(f8,conjecture,(
% 0.21/0.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    ~spl3_1 | ~spl3_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f20,f34,f30])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) | k2_relset_1(sK0,sK1,sK2) != k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))),
% 0.21/0.41    inference(cnf_transformation,[],[f18])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (25333)------------------------------
% 0.21/0.41  % (25333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (25333)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (25333)Memory used [KB]: 10618
% 0.21/0.41  % (25333)Time elapsed: 0.009 s
% 0.21/0.41  % (25333)------------------------------
% 0.21/0.41  % (25333)------------------------------
% 0.21/0.42  % (25325)Success in time 0.069 s
%------------------------------------------------------------------------------
