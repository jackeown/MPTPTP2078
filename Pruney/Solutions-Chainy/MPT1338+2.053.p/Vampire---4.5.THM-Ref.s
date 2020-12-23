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
% DateTime   : Thu Dec  3 13:14:08 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 426 expanded)
%              Number of leaves         :   41 ( 176 expanded)
%              Depth                    :   12
%              Number of atoms          :  578 (1812 expanded)
%              Number of equality atoms :  154 ( 503 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f112,f117,f122,f152,f157,f162,f169,f185,f215,f221,f229,f238,f288,f333,f347,f358])).

fof(f358,plain,
    ( spl3_18
    | ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl3_18
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f354,f228])).

fof(f228,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f354,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_36 ),
    inference(superposition,[],[f71,f346])).

fof(f346,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl3_36
  <=> k1_relat_1(sK2) = k2_relat_1(k6_partfun1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f53])).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f347,plain,
    ( spl3_36
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_28
    | spl3_34 ),
    inference(avatar_split_clause,[],[f340,f325,f285,f159,f154,f149,f97,f92,f344])).

fof(f92,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f97,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f149,plain,
    ( spl3_11
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f154,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f159,plain,
    ( spl3_13
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f285,plain,
    ( spl3_28
  <=> k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f325,plain,
    ( spl3_34
  <=> o_0_0_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f340,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_28
    | spl3_34 ),
    inference(backward_demodulation,[],[f287,f338])).

fof(f338,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_34 ),
    inference(unit_resulting_resolution,[],[f94,f99,f151,f156,f161,f326,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | o_0_0_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f69,f51])).

fof(f51,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f326,plain,
    ( o_0_0_xboole_0 != k2_struct_0(sK1)
    | spl3_34 ),
    inference(avatar_component_clause,[],[f325])).

fof(f161,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f156,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f151,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f99,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f94,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f287,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f285])).

fof(f333,plain,
    ( o_0_0_xboole_0 != k1_struct_0(sK0)
    | o_0_0_xboole_0 != k2_struct_0(sK1)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f288,plain,
    ( spl3_28
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f191,f182,f97,f92,f285])).

fof(f182,plain,
    ( spl3_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f191,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f190,f184])).

fof(f184,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f182])).

fof(f190,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f189,f94])).

fof(f189,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f62,f99])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f238,plain,
    ( spl3_19
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f123,f77,f235])).

fof(f235,plain,
    ( spl3_19
  <=> o_0_0_xboole_0 = k1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f77,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f123,plain,
    ( o_0_0_xboole_0 = k1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f79,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | o_0_0_xboole_0 = k1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f51])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f79,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f229,plain,
    ( ~ spl3_18
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_17 ),
    inference(avatar_split_clause,[],[f222,f212,f159,f154,f149,f97,f92,f226])).

fof(f212,plain,
    ( spl3_17
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f222,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_17 ),
    inference(forward_demodulation,[],[f219,f201])).

fof(f201,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f200,f179])).

fof(f179,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f156,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f200,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f198,f177])).

fof(f177,plain,
    ( k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f175,f174])).

fof(f174,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f173,f170])).

fof(f170,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f156,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f173,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f172,f94])).

fof(f172,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f60,f99])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f175,plain,
    ( k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f156,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f198,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f156,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

fof(f219,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_17 ),
    inference(backward_demodulation,[],[f214,f216])).

fof(f216,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f94,f99,f151,f156,f161,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f214,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f212])).

fof(f221,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_16 ),
    inference(subsumption_resolution,[],[f218,f195])).

fof(f195,plain,
    ( k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f194,f161])).

fof(f194,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f192,f177])).

fof(f192,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f156,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f218,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | spl3_16 ),
    inference(backward_demodulation,[],[f210,f216])).

fof(f210,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl3_16
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f215,plain,
    ( ~ spl3_16
    | ~ spl3_17
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f147,f87,f77,f212,f208])).

fof(f87,plain,
    ( spl3_3
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f147,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f143,f134])).

fof(f134,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f79,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f143,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f142,f134])).

fof(f142,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f141,f135])).

fof(f135,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f89,f58])).

fof(f89,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f141,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f50,f135])).

fof(f50,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
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
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f185,plain,
    ( spl3_15
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f170,f154,f182])).

fof(f169,plain,
    ( ~ spl3_14
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f164,f87,f82,f166])).

fof(f166,plain,
    ( spl3_14
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f82,plain,
    ( spl3_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f164,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f163,f135])).

fof(f163,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f84,f89,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f84,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f162,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f146,f119,f87,f77,f159])).

fof(f119,plain,
    ( spl3_9
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f146,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f138,f134])).

fof(f138,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f121,f135])).

fof(f121,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f157,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f145,f109,f87,f77,f154])).

fof(f109,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f139,f134])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f111,f135])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f152,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f144,f102,f87,f77,f149])).

fof(f102,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f144,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f140,f134])).

fof(f140,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f104,f135])).

fof(f104,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f122,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f48,f119])).

fof(f48,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f117,plain,
    ( spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f106,f77,f114])).

fof(f114,plain,
    ( spl3_8
  <=> v1_xboole_0(k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f106,plain,
    ( v1_xboole_0(k1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f79,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).

fof(f112,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f47,f109])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f102])).

fof(f46,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f49,f97])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f44,f87])).

fof(f44,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f42,f77])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:00:42 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.43  % (26205)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.44  % (26205)Refutation found. Thanks to Tanya!
% 0.23/0.44  % SZS status Theorem for theBenchmark
% 0.23/0.44  % SZS output start Proof for theBenchmark
% 0.23/0.44  fof(f359,plain,(
% 0.23/0.44    $false),
% 0.23/0.44    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f112,f117,f122,f152,f157,f162,f169,f185,f215,f221,f229,f238,f288,f333,f347,f358])).
% 0.23/0.44  fof(f358,plain,(
% 0.23/0.44    spl3_18 | ~spl3_36),
% 0.23/0.44    inference(avatar_contradiction_clause,[],[f357])).
% 0.23/0.44  fof(f357,plain,(
% 0.23/0.44    $false | (spl3_18 | ~spl3_36)),
% 0.23/0.44    inference(subsumption_resolution,[],[f354,f228])).
% 0.23/0.44  fof(f228,plain,(
% 0.23/0.44    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_18),
% 0.23/0.44    inference(avatar_component_clause,[],[f226])).
% 0.23/0.44  fof(f226,plain,(
% 0.23/0.44    spl3_18 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.23/0.44  fof(f354,plain,(
% 0.23/0.44    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_36),
% 0.23/0.44    inference(superposition,[],[f71,f346])).
% 0.23/0.44  fof(f346,plain,(
% 0.23/0.44    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(k2_struct_0(sK0))) | ~spl3_36),
% 0.23/0.44    inference(avatar_component_clause,[],[f344])).
% 0.23/0.44  fof(f344,plain,(
% 0.23/0.44    spl3_36 <=> k1_relat_1(sK2) = k2_relat_1(k6_partfun1(k2_struct_0(sK0)))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.23/0.44  fof(f71,plain,(
% 0.23/0.44    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.23/0.44    inference(definition_unfolding,[],[f55,f53])).
% 0.23/0.44  fof(f53,plain,(
% 0.23/0.44    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f9])).
% 0.23/0.44  fof(f9,axiom,(
% 0.23/0.44    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.23/0.44  fof(f55,plain,(
% 0.23/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.44    inference(cnf_transformation,[],[f2])).
% 0.23/0.44  fof(f2,axiom,(
% 0.23/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.23/0.44  fof(f347,plain,(
% 0.23/0.44    spl3_36 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_28 | spl3_34),
% 0.23/0.44    inference(avatar_split_clause,[],[f340,f325,f285,f159,f154,f149,f97,f92,f344])).
% 0.23/0.44  fof(f92,plain,(
% 0.23/0.44    spl3_4 <=> v1_funct_1(sK2)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.44  fof(f97,plain,(
% 0.23/0.44    spl3_5 <=> v2_funct_1(sK2)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.44  fof(f149,plain,(
% 0.23/0.44    spl3_11 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.23/0.44  fof(f154,plain,(
% 0.23/0.44    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.23/0.44  fof(f159,plain,(
% 0.23/0.44    spl3_13 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.23/0.44  fof(f285,plain,(
% 0.23/0.44    spl3_28 <=> k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.23/0.44  fof(f325,plain,(
% 0.23/0.44    spl3_34 <=> o_0_0_xboole_0 = k2_struct_0(sK1)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.23/0.44  fof(f340,plain,(
% 0.23/0.44    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(k2_struct_0(sK0))) | (~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_28 | spl3_34)),
% 0.23/0.44    inference(backward_demodulation,[],[f287,f338])).
% 0.23/0.44  fof(f338,plain,(
% 0.23/0.44    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) | (~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_34)),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f94,f99,f151,f156,f161,f326,f75])).
% 0.23/0.44  fof(f75,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | o_0_0_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.23/0.44    inference(definition_unfolding,[],[f69,f51])).
% 0.23/0.44  fof(f51,plain,(
% 0.23/0.44    k1_xboole_0 = o_0_0_xboole_0),
% 0.23/0.44    inference(cnf_transformation,[],[f1])).
% 0.23/0.44  fof(f1,axiom,(
% 0.23/0.44    k1_xboole_0 = o_0_0_xboole_0),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.23/0.44  fof(f69,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f37])).
% 0.23/0.44  fof(f37,plain,(
% 0.23/0.44    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.23/0.44    inference(flattening,[],[f36])).
% 0.23/0.44  fof(f36,plain,(
% 0.23/0.44    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.23/0.44    inference(ennf_transformation,[],[f11])).
% 0.23/0.44  fof(f11,axiom,(
% 0.23/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.23/0.44  fof(f326,plain,(
% 0.23/0.44    o_0_0_xboole_0 != k2_struct_0(sK1) | spl3_34),
% 0.23/0.44    inference(avatar_component_clause,[],[f325])).
% 0.23/0.44  fof(f161,plain,(
% 0.23/0.44    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.23/0.44    inference(avatar_component_clause,[],[f159])).
% 0.23/0.44  fof(f156,plain,(
% 0.23/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_12),
% 0.23/0.44    inference(avatar_component_clause,[],[f154])).
% 0.23/0.44  fof(f151,plain,(
% 0.23/0.44    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_11),
% 0.23/0.44    inference(avatar_component_clause,[],[f149])).
% 0.23/0.44  fof(f99,plain,(
% 0.23/0.44    v2_funct_1(sK2) | ~spl3_5),
% 0.23/0.44    inference(avatar_component_clause,[],[f97])).
% 0.23/0.44  fof(f94,plain,(
% 0.23/0.44    v1_funct_1(sK2) | ~spl3_4),
% 0.23/0.44    inference(avatar_component_clause,[],[f92])).
% 0.23/0.44  fof(f287,plain,(
% 0.23/0.44    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~spl3_28),
% 0.23/0.44    inference(avatar_component_clause,[],[f285])).
% 0.23/0.44  fof(f333,plain,(
% 0.23/0.44    o_0_0_xboole_0 != k1_struct_0(sK0) | o_0_0_xboole_0 != k2_struct_0(sK1) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_xboole_0(k1_struct_0(sK0))),
% 0.23/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.44  fof(f288,plain,(
% 0.23/0.44    spl3_28 | ~spl3_4 | ~spl3_5 | ~spl3_15),
% 0.23/0.44    inference(avatar_split_clause,[],[f191,f182,f97,f92,f285])).
% 0.23/0.44  fof(f182,plain,(
% 0.23/0.44    spl3_15 <=> v1_relat_1(sK2)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.23/0.44  fof(f191,plain,(
% 0.23/0.44    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | (~spl3_4 | ~spl3_5 | ~spl3_15)),
% 0.23/0.44    inference(subsumption_resolution,[],[f190,f184])).
% 0.23/0.44  fof(f184,plain,(
% 0.23/0.44    v1_relat_1(sK2) | ~spl3_15),
% 0.23/0.44    inference(avatar_component_clause,[],[f182])).
% 0.23/0.44  fof(f190,plain,(
% 0.23/0.44    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.23/0.44    inference(subsumption_resolution,[],[f189,f94])).
% 0.23/0.44  fof(f189,plain,(
% 0.23/0.44    k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.23/0.44    inference(resolution,[],[f62,f99])).
% 0.23/0.44  fof(f62,plain,(
% 0.23/0.44    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f29])).
% 0.23/0.44  fof(f29,plain,(
% 0.23/0.44    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.44    inference(flattening,[],[f28])).
% 0.23/0.44  fof(f28,plain,(
% 0.23/0.44    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f4])).
% 0.23/0.44  fof(f4,axiom,(
% 0.23/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0))))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.23/0.44  fof(f238,plain,(
% 0.23/0.44    spl3_19 | ~spl3_1),
% 0.23/0.44    inference(avatar_split_clause,[],[f123,f77,f235])).
% 0.23/0.44  fof(f235,plain,(
% 0.23/0.44    spl3_19 <=> o_0_0_xboole_0 = k1_struct_0(sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.23/0.44  fof(f77,plain,(
% 0.23/0.44    spl3_1 <=> l1_struct_0(sK0)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.44  fof(f123,plain,(
% 0.23/0.44    o_0_0_xboole_0 = k1_struct_0(sK0) | ~spl3_1),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f79,f73])).
% 0.23/0.44  fof(f73,plain,(
% 0.23/0.44    ( ! [X0] : (~l1_struct_0(X0) | o_0_0_xboole_0 = k1_struct_0(X0)) )),
% 0.23/0.44    inference(definition_unfolding,[],[f57,f51])).
% 0.23/0.44  fof(f57,plain,(
% 0.23/0.44    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f22])).
% 0.23/0.44  fof(f22,plain,(
% 0.23/0.44    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.23/0.44    inference(ennf_transformation,[],[f12])).
% 0.23/0.44  fof(f12,axiom,(
% 0.23/0.44    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 0.23/0.44  fof(f79,plain,(
% 0.23/0.44    l1_struct_0(sK0) | ~spl3_1),
% 0.23/0.44    inference(avatar_component_clause,[],[f77])).
% 0.23/0.44  fof(f229,plain,(
% 0.23/0.44    ~spl3_18 | ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_17),
% 0.23/0.44    inference(avatar_split_clause,[],[f222,f212,f159,f154,f149,f97,f92,f226])).
% 0.23/0.44  fof(f212,plain,(
% 0.23/0.44    spl3_17 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.23/0.44  fof(f222,plain,(
% 0.23/0.44    k2_struct_0(sK0) != k1_relat_1(sK2) | (~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_17)),
% 0.23/0.44    inference(forward_demodulation,[],[f219,f201])).
% 0.23/0.44  fof(f201,plain,(
% 0.23/0.44    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.23/0.44    inference(forward_demodulation,[],[f200,f179])).
% 0.23/0.44  fof(f179,plain,(
% 0.23/0.44    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) | ~spl3_12),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f156,f65])).
% 0.23/0.44  fof(f65,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f32])).
% 0.23/0.44  fof(f32,plain,(
% 0.23/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.44    inference(ennf_transformation,[],[f6])).
% 0.23/0.44  fof(f6,axiom,(
% 0.23/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.23/0.44  fof(f200,plain,(
% 0.23/0.44    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.23/0.44    inference(forward_demodulation,[],[f198,f177])).
% 0.23/0.44  fof(f177,plain,(
% 0.23/0.44    k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.23/0.44    inference(forward_demodulation,[],[f175,f174])).
% 0.23/0.44  fof(f174,plain,(
% 0.23/0.44    k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.23/0.44    inference(subsumption_resolution,[],[f173,f170])).
% 0.23/0.44  fof(f170,plain,(
% 0.23/0.44    v1_relat_1(sK2) | ~spl3_12),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f156,f63])).
% 0.23/0.44  fof(f63,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f30])).
% 0.23/0.44  fof(f30,plain,(
% 0.23/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.44    inference(ennf_transformation,[],[f5])).
% 0.23/0.44  fof(f5,axiom,(
% 0.23/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.23/0.44  fof(f173,plain,(
% 0.23/0.44    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.23/0.44    inference(subsumption_resolution,[],[f172,f94])).
% 0.23/0.44  fof(f172,plain,(
% 0.23/0.44    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.23/0.44    inference(resolution,[],[f60,f99])).
% 0.23/0.44  fof(f60,plain,(
% 0.23/0.44    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(X0) = k4_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f27])).
% 0.23/0.44  fof(f27,plain,(
% 0.23/0.44    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.44    inference(flattening,[],[f26])).
% 0.23/0.44  fof(f26,plain,(
% 0.23/0.44    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f3])).
% 0.23/0.44  fof(f3,axiom,(
% 0.23/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.23/0.44  fof(f175,plain,(
% 0.23/0.44    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_12),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f156,f64])).
% 0.23/0.44  fof(f64,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f31])).
% 0.23/0.44  fof(f31,plain,(
% 0.23/0.44    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.44    inference(ennf_transformation,[],[f7])).
% 0.23/0.44  fof(f7,axiom,(
% 0.23/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.23/0.44  fof(f198,plain,(
% 0.23/0.44    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~spl3_12),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f156,f67])).
% 0.23/0.44  fof(f67,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) )),
% 0.23/0.44    inference(cnf_transformation,[],[f33])).
% 0.23/0.44  fof(f33,plain,(
% 0.23/0.44    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.44    inference(ennf_transformation,[],[f8])).
% 0.23/0.44  fof(f8,axiom,(
% 0.23/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).
% 0.23/0.44  fof(f219,plain,(
% 0.23/0.44    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_17)),
% 0.23/0.44    inference(backward_demodulation,[],[f214,f216])).
% 0.23/0.44  fof(f216,plain,(
% 0.23/0.44    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | (~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13)),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f94,f99,f151,f156,f161,f68])).
% 0.23/0.44  fof(f68,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f35])).
% 0.23/0.44  fof(f35,plain,(
% 0.23/0.44    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.23/0.44    inference(flattening,[],[f34])).
% 0.23/0.44  fof(f34,plain,(
% 0.23/0.44    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.23/0.44    inference(ennf_transformation,[],[f16])).
% 0.23/0.44  fof(f16,axiom,(
% 0.23/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.23/0.44  fof(f214,plain,(
% 0.23/0.44    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_17),
% 0.23/0.44    inference(avatar_component_clause,[],[f212])).
% 0.23/0.44  fof(f221,plain,(
% 0.23/0.44    ~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_16),
% 0.23/0.44    inference(avatar_contradiction_clause,[],[f220])).
% 0.23/0.44  fof(f220,plain,(
% 0.23/0.44    $false | (~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_16)),
% 0.23/0.44    inference(subsumption_resolution,[],[f218,f195])).
% 0.23/0.44  fof(f195,plain,(
% 0.23/0.44    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_12 | ~spl3_13)),
% 0.23/0.44    inference(forward_demodulation,[],[f194,f161])).
% 0.23/0.44  fof(f194,plain,(
% 0.23/0.44    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.23/0.44    inference(forward_demodulation,[],[f192,f177])).
% 0.23/0.44  fof(f192,plain,(
% 0.23/0.44    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~spl3_12),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f156,f66])).
% 0.23/0.44  fof(f66,plain,(
% 0.23/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f33])).
% 0.23/0.44  fof(f218,plain,(
% 0.23/0.44    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_11 | ~spl3_12 | ~spl3_13 | spl3_16)),
% 0.23/0.44    inference(backward_demodulation,[],[f210,f216])).
% 0.23/0.44  fof(f210,plain,(
% 0.23/0.44    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_16),
% 0.23/0.44    inference(avatar_component_clause,[],[f208])).
% 0.23/0.44  fof(f208,plain,(
% 0.23/0.44    spl3_16 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.23/0.44  fof(f215,plain,(
% 0.23/0.44    ~spl3_16 | ~spl3_17 | ~spl3_1 | ~spl3_3),
% 0.23/0.44    inference(avatar_split_clause,[],[f147,f87,f77,f212,f208])).
% 0.23/0.44  fof(f87,plain,(
% 0.23/0.44    spl3_3 <=> l1_struct_0(sK1)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.44  fof(f147,plain,(
% 0.23/0.44    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_1 | ~spl3_3)),
% 0.23/0.44    inference(forward_demodulation,[],[f143,f134])).
% 0.23/0.44  fof(f134,plain,(
% 0.23/0.44    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_1),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f79,f58])).
% 0.23/0.44  fof(f58,plain,(
% 0.23/0.44    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f23])).
% 0.23/0.44  fof(f23,plain,(
% 0.23/0.44    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.23/0.44    inference(ennf_transformation,[],[f13])).
% 0.23/0.44  fof(f13,axiom,(
% 0.23/0.44    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.23/0.44  fof(f143,plain,(
% 0.23/0.44    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_1 | ~spl3_3)),
% 0.23/0.44    inference(backward_demodulation,[],[f142,f134])).
% 0.23/0.44  fof(f142,plain,(
% 0.23/0.44    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~spl3_3),
% 0.23/0.44    inference(forward_demodulation,[],[f141,f135])).
% 0.23/0.44  fof(f135,plain,(
% 0.23/0.44    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_3),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f89,f58])).
% 0.23/0.44  fof(f89,plain,(
% 0.23/0.44    l1_struct_0(sK1) | ~spl3_3),
% 0.23/0.44    inference(avatar_component_clause,[],[f87])).
% 0.23/0.44  fof(f141,plain,(
% 0.23/0.44    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl3_3),
% 0.23/0.44    inference(backward_demodulation,[],[f50,f135])).
% 0.23/0.44  fof(f50,plain,(
% 0.23/0.44    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.23/0.44    inference(cnf_transformation,[],[f41])).
% 0.23/0.44  fof(f41,plain,(
% 0.23/0.44    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.23/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f40,f39,f38])).
% 0.23/0.44  fof(f38,plain,(
% 0.23/0.44    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f39,plain,(
% 0.23/0.44    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f40,plain,(
% 0.23/0.44    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f20,plain,(
% 0.23/0.44    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.23/0.44    inference(flattening,[],[f19])).
% 0.23/0.44  fof(f19,plain,(
% 0.23/0.44    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.23/0.44    inference(ennf_transformation,[],[f18])).
% 0.23/0.44  fof(f18,negated_conjecture,(
% 0.23/0.44    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.23/0.44    inference(negated_conjecture,[],[f17])).
% 0.23/0.44  fof(f17,conjecture,(
% 0.23/0.44    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.23/0.44  fof(f185,plain,(
% 0.23/0.44    spl3_15 | ~spl3_12),
% 0.23/0.44    inference(avatar_split_clause,[],[f170,f154,f182])).
% 0.23/0.44  fof(f169,plain,(
% 0.23/0.44    ~spl3_14 | spl3_2 | ~spl3_3),
% 0.23/0.44    inference(avatar_split_clause,[],[f164,f87,f82,f166])).
% 0.23/0.44  fof(f166,plain,(
% 0.23/0.44    spl3_14 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.23/0.44  fof(f82,plain,(
% 0.23/0.44    spl3_2 <=> v2_struct_0(sK1)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.44  fof(f164,plain,(
% 0.23/0.44    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_2 | ~spl3_3)),
% 0.23/0.44    inference(forward_demodulation,[],[f163,f135])).
% 0.23/0.44  fof(f163,plain,(
% 0.23/0.44    ~v1_xboole_0(u1_struct_0(sK1)) | (spl3_2 | ~spl3_3)),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f84,f89,f59])).
% 0.23/0.44  fof(f59,plain,(
% 0.23/0.44    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f25])).
% 0.23/0.44  fof(f25,plain,(
% 0.23/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.23/0.44    inference(flattening,[],[f24])).
% 0.23/0.44  fof(f24,plain,(
% 0.23/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.23/0.44    inference(ennf_transformation,[],[f14])).
% 0.23/0.44  fof(f14,axiom,(
% 0.23/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.23/0.44  fof(f84,plain,(
% 0.23/0.44    ~v2_struct_0(sK1) | spl3_2),
% 0.23/0.44    inference(avatar_component_clause,[],[f82])).
% 0.23/0.44  fof(f162,plain,(
% 0.23/0.44    spl3_13 | ~spl3_1 | ~spl3_3 | ~spl3_9),
% 0.23/0.44    inference(avatar_split_clause,[],[f146,f119,f87,f77,f159])).
% 0.23/0.44  fof(f119,plain,(
% 0.23/0.44    spl3_9 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.23/0.44  fof(f146,plain,(
% 0.23/0.44    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_3 | ~spl3_9)),
% 0.23/0.44    inference(backward_demodulation,[],[f138,f134])).
% 0.23/0.44  fof(f138,plain,(
% 0.23/0.44    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_9)),
% 0.23/0.44    inference(backward_demodulation,[],[f121,f135])).
% 0.23/0.44  fof(f121,plain,(
% 0.23/0.44    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_9),
% 0.23/0.44    inference(avatar_component_clause,[],[f119])).
% 0.23/0.44  fof(f157,plain,(
% 0.23/0.44    spl3_12 | ~spl3_1 | ~spl3_3 | ~spl3_7),
% 0.23/0.44    inference(avatar_split_clause,[],[f145,f109,f87,f77,f154])).
% 0.23/0.44  fof(f109,plain,(
% 0.23/0.44    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.44  fof(f145,plain,(
% 0.23/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_1 | ~spl3_3 | ~spl3_7)),
% 0.23/0.44    inference(backward_demodulation,[],[f139,f134])).
% 0.23/0.44  fof(f139,plain,(
% 0.23/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_3 | ~spl3_7)),
% 0.23/0.44    inference(backward_demodulation,[],[f111,f135])).
% 0.23/0.44  fof(f111,plain,(
% 0.23/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_7),
% 0.23/0.44    inference(avatar_component_clause,[],[f109])).
% 0.23/0.44  fof(f152,plain,(
% 0.23/0.44    spl3_11 | ~spl3_1 | ~spl3_3 | ~spl3_6),
% 0.23/0.44    inference(avatar_split_clause,[],[f144,f102,f87,f77,f149])).
% 0.23/0.44  fof(f102,plain,(
% 0.23/0.44    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.44  fof(f144,plain,(
% 0.23/0.44    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_1 | ~spl3_3 | ~spl3_6)),
% 0.23/0.44    inference(backward_demodulation,[],[f140,f134])).
% 0.23/0.44  fof(f140,plain,(
% 0.23/0.44    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_3 | ~spl3_6)),
% 0.23/0.44    inference(backward_demodulation,[],[f104,f135])).
% 0.23/0.44  fof(f104,plain,(
% 0.23/0.44    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.23/0.44    inference(avatar_component_clause,[],[f102])).
% 0.23/0.44  fof(f122,plain,(
% 0.23/0.44    spl3_9),
% 0.23/0.44    inference(avatar_split_clause,[],[f48,f119])).
% 0.23/0.44  fof(f48,plain,(
% 0.23/0.44    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.23/0.44    inference(cnf_transformation,[],[f41])).
% 0.23/0.44  fof(f117,plain,(
% 0.23/0.44    spl3_8 | ~spl3_1),
% 0.23/0.44    inference(avatar_split_clause,[],[f106,f77,f114])).
% 0.23/0.44  fof(f114,plain,(
% 0.23/0.44    spl3_8 <=> v1_xboole_0(k1_struct_0(sK0))),
% 0.23/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.44  fof(f106,plain,(
% 0.23/0.44    v1_xboole_0(k1_struct_0(sK0)) | ~spl3_1),
% 0.23/0.44    inference(unit_resulting_resolution,[],[f79,f56])).
% 0.23/0.44  fof(f56,plain,(
% 0.23/0.44    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f21])).
% 0.23/0.44  fof(f21,plain,(
% 0.23/0.44    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.23/0.44    inference(ennf_transformation,[],[f15])).
% 0.23/0.44  fof(f15,axiom,(
% 0.23/0.44    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_struct_0)).
% 0.23/0.44  fof(f112,plain,(
% 0.23/0.44    spl3_7),
% 0.23/0.44    inference(avatar_split_clause,[],[f47,f109])).
% 0.23/0.44  fof(f47,plain,(
% 0.23/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.23/0.44    inference(cnf_transformation,[],[f41])).
% 0.23/0.44  fof(f105,plain,(
% 0.23/0.44    spl3_6),
% 0.23/0.44    inference(avatar_split_clause,[],[f46,f102])).
% 0.23/0.44  fof(f46,plain,(
% 0.23/0.44    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.23/0.44    inference(cnf_transformation,[],[f41])).
% 0.23/0.44  fof(f100,plain,(
% 0.23/0.44    spl3_5),
% 0.23/0.44    inference(avatar_split_clause,[],[f49,f97])).
% 0.23/0.44  fof(f49,plain,(
% 0.23/0.44    v2_funct_1(sK2)),
% 0.23/0.44    inference(cnf_transformation,[],[f41])).
% 0.23/0.44  fof(f95,plain,(
% 0.23/0.44    spl3_4),
% 0.23/0.44    inference(avatar_split_clause,[],[f45,f92])).
% 0.23/0.44  fof(f45,plain,(
% 0.23/0.44    v1_funct_1(sK2)),
% 0.23/0.44    inference(cnf_transformation,[],[f41])).
% 0.23/0.44  fof(f90,plain,(
% 0.23/0.44    spl3_3),
% 0.23/0.44    inference(avatar_split_clause,[],[f44,f87])).
% 0.23/0.44  fof(f44,plain,(
% 0.23/0.44    l1_struct_0(sK1)),
% 0.23/0.44    inference(cnf_transformation,[],[f41])).
% 0.23/0.44  fof(f85,plain,(
% 0.23/0.44    ~spl3_2),
% 0.23/0.44    inference(avatar_split_clause,[],[f43,f82])).
% 0.23/0.44  fof(f43,plain,(
% 0.23/0.44    ~v2_struct_0(sK1)),
% 0.23/0.44    inference(cnf_transformation,[],[f41])).
% 0.23/0.44  fof(f80,plain,(
% 0.23/0.44    spl3_1),
% 0.23/0.44    inference(avatar_split_clause,[],[f42,f77])).
% 0.23/0.44  fof(f42,plain,(
% 0.23/0.44    l1_struct_0(sK0)),
% 0.23/0.44    inference(cnf_transformation,[],[f41])).
% 0.23/0.44  % SZS output end Proof for theBenchmark
% 0.23/0.44  % (26205)------------------------------
% 0.23/0.44  % (26205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.44  % (26205)Termination reason: Refutation
% 0.23/0.44  
% 0.23/0.44  % (26205)Memory used [KB]: 10874
% 0.23/0.44  % (26205)Time elapsed: 0.014 s
% 0.23/0.44  % (26205)------------------------------
% 0.23/0.44  % (26205)------------------------------
% 0.23/0.44  % (26189)Success in time 0.075 s
%------------------------------------------------------------------------------
