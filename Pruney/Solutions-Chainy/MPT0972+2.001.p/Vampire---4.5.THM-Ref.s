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
% DateTime   : Thu Dec  3 13:01:04 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 441 expanded)
%              Number of leaves         :   37 ( 173 expanded)
%              Depth                    :   16
%              Number of atoms          :  691 (1707 expanded)
%              Number of equality atoms :  150 ( 459 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f882,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f94,f99,f108,f113,f118,f139,f144,f167,f183,f191,f207,f216,f292,f322,f324,f338,f344,f361,f374,f377,f565,f639,f644,f647,f648,f649,f802,f845,f881])).

fof(f881,plain,
    ( ~ spl8_7
    | spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_27 ),
    inference(avatar_contradiction_clause,[],[f880])).

fof(f880,plain,
    ( $false
    | ~ spl8_7
    | spl8_8
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f879,f148])).

fof(f148,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl8_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f879,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_7
    | spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f878,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f878,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_7
    | spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f875,f866])).

fof(f866,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_7
    | spl8_8
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f865,f656])).

fof(f656,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_7
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_27 ),
    inference(global_subsumption,[],[f215])).

fof(f215,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl8_18
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f865,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK3)
    | spl8_8
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f121,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f121,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f875,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_21 ),
    inference(resolution,[],[f297,f72])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f297,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl8_21
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f845,plain,
    ( ~ spl8_34
    | ~ spl8_17
    | spl8_30 ),
    inference(avatar_split_clause,[],[f768,f401,f209,f562])).

fof(f562,plain,
    ( spl8_34
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f209,plain,
    ( spl8_17
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f401,plain,
    ( spl8_30
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f768,plain,
    ( k1_xboole_0 != sK2
    | ~ spl8_17
    | spl8_30 ),
    inference(backward_demodulation,[],[f402,f211])).

fof(f211,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f209])).

fof(f402,plain,
    ( sK2 != sK3
    | spl8_30 ),
    inference(avatar_component_clause,[],[f401])).

fof(f802,plain,
    ( ~ spl8_4
    | ~ spl8_7
    | spl8_13
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_7
    | spl8_13
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f800,f182])).

fof(f182,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl8_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f800,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_4
    | ~ spl8_7
    | spl8_13
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f799,f70])).

fof(f799,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_7
    | spl8_13
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f796,f288])).

fof(f288,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_4
    | ~ spl8_7
    | spl8_13
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f254,f215])).

fof(f254,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl8_4
    | ~ spl8_7
    | spl8_13 ),
    inference(backward_demodulation,[],[f165,f251])).

fof(f251,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_4
    | ~ spl8_7
    | spl8_13 ),
    inference(subsumption_resolution,[],[f234,f165])).

fof(f234,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f220,f117])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f220,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_4 ),
    inference(resolution,[],[f98,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f165,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_13
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f796,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_22 ),
    inference(resolution,[],[f321,f72])).

fof(f321,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl8_22
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f649,plain,
    ( k1_xboole_0 != sK1
    | r2_relset_1(sK0,k1_xboole_0,sK2,sK2)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f648,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f647,plain,
    ( ~ spl8_7
    | spl8_37 ),
    inference(avatar_contradiction_clause,[],[f646])).

fof(f646,plain,
    ( $false
    | ~ spl8_7
    | spl8_37 ),
    inference(subsumption_resolution,[],[f645,f117])).

fof(f645,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_37 ),
    inference(resolution,[],[f637,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X1,X2,X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(condensation,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f637,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl8_37 ),
    inference(avatar_component_clause,[],[f635])).

fof(f635,plain,
    ( spl8_37
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f644,plain,
    ( ~ spl8_38
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | spl8_16
    | ~ spl8_19
    | ~ spl8_24
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f618,f372,f368,f348,f229,f204,f188,f84,f79,f641])).

fof(f641,plain,
    ( spl8_38
  <=> r2_relset_1(sK0,k1_xboole_0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f79,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f84,plain,
    ( spl8_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f188,plain,
    ( spl8_15
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f204,plain,
    ( spl8_16
  <=> r2_relset_1(sK0,k1_xboole_0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f229,plain,
    ( spl8_19
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f348,plain,
    ( spl8_24
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f368,plain,
    ( spl8_27
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f372,plain,
    ( spl8_28
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK2 = X0
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f618,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK2)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | spl8_16
    | ~ spl8_19
    | ~ spl8_24
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f206,f609])).

fof(f609,plain,
    ( sK2 = sK3
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_19
    | ~ spl8_24
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f608,f349])).

fof(f349,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f348])).

fof(f608,plain,
    ( sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_19
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f607,f81])).

fof(f81,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f607,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_19
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f606,f190])).

fof(f190,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f606,plain,
    ( sK2 = sK3
    | sK0 != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_2
    | ~ spl8_19
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(trivial_inequality_removal,[],[f605])).

fof(f605,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | sK0 != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_2
    | ~ spl8_19
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(duplicate_literal_removal,[],[f604])).

fof(f604,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | sK0 != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK0 != k1_relat_1(sK3)
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl8_2
    | ~ spl8_19
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(superposition,[],[f373,f587])).

fof(f587,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4(sK2,X0)) = k1_funct_1(sK3,sK4(sK2,X0))
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | sK2 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl8_2
    | ~ spl8_19
    | ~ spl8_27 ),
    inference(resolution,[],[f538,f31])).

fof(f31,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f538,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | sK2 = X0 )
    | ~ spl8_2
    | ~ spl8_19
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f537,f369])).

fof(f369,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f368])).

fof(f537,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | sK2 = X0 )
    | ~ spl8_2
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f536,f86])).

fof(f86,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f536,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | sK2 = X0 )
    | ~ spl8_19 ),
    inference(superposition,[],[f41,f231])).

fof(f231,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f229])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f373,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | sK2 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f372])).

fof(f206,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3)
    | spl8_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f639,plain,
    ( spl8_30
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_15
    | ~ spl8_19
    | ~ spl8_24
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f609,f372,f368,f348,f229,f188,f84,f79,f401])).

fof(f565,plain,
    ( spl8_34
    | ~ spl8_14
    | ~ spl8_11
    | spl8_18 ),
    inference(avatar_split_clause,[],[f498,f213,f141,f180,f562])).

fof(f141,plain,
    ( spl8_11
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f498,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2
    | ~ spl8_11
    | spl8_18 ),
    inference(forward_demodulation,[],[f497,f70])).

fof(f497,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_11
    | spl8_18 ),
    inference(subsumption_resolution,[],[f495,f214])).

fof(f214,plain,
    ( k1_xboole_0 != sK0
    | spl8_18 ),
    inference(avatar_component_clause,[],[f213])).

fof(f495,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_11 ),
    inference(resolution,[],[f143,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f143,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f377,plain,
    ( ~ spl8_7
    | spl8_27 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl8_7
    | spl8_27 ),
    inference(subsumption_resolution,[],[f117,f375])).

fof(f375,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl8_27 ),
    inference(resolution,[],[f370,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f370,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f368])).

fof(f374,plain,
    ( ~ spl8_27
    | spl8_28
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f331,f164,f115,f84,f372,f368])).

fof(f331,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | sK2 = X0 )
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f89,f226])).

fof(f226,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f224,f117])).

fof(f224,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_13 ),
    inference(superposition,[],[f166,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f166,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | sK2 = X0 )
    | ~ spl8_2 ),
    inference(resolution,[],[f86,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f361,plain,
    ( ~ spl8_6
    | spl8_24 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | ~ spl8_6
    | spl8_24 ),
    inference(subsumption_resolution,[],[f112,f359])).

fof(f359,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl8_24 ),
    inference(resolution,[],[f350,f57])).

fof(f350,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f348])).

fof(f112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f344,plain,
    ( spl8_8
    | ~ spl8_3
    | ~ spl8_6
    | spl8_9 ),
    inference(avatar_split_clause,[],[f218,f124,f110,f91,f120])).

fof(f91,plain,
    ( spl8_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f218,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_3
    | ~ spl8_6
    | spl8_9 ),
    inference(subsumption_resolution,[],[f192,f125])).

fof(f125,plain,
    ( k1_xboole_0 != sK1
    | spl8_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f185,f112])).

fof(f185,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(resolution,[],[f93,f66])).

fof(f93,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f338,plain,
    ( spl8_19
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f226,f164,f115,f229])).

fof(f324,plain,
    ( spl8_21
    | ~ spl8_10
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f300,f213,f136,f295])).

fof(f136,plain,
    ( spl8_10
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f300,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_10
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f138,f215])).

fof(f138,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f322,plain,
    ( spl8_22
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f283,f213,f141,f319])).

fof(f283,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f143,f215])).

fof(f292,plain,
    ( spl8_12
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f133,f124,f110,f146])).

fof(f133,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f131,f70])).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f112,f126])).

fof(f216,plain,
    ( spl8_17
    | spl8_18
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f169,f146,f136,f213,f209])).

fof(f169,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f155,f148])).

fof(f155,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f153,f70])).

fof(f153,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_10 ),
    inference(resolution,[],[f138,f74])).

fof(f207,plain,
    ( ~ spl8_16
    | spl8_5
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f130,f124,f105,f204])).

fof(f105,plain,
    ( spl8_5
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f130,plain,
    ( ~ r2_relset_1(sK0,k1_xboole_0,sK2,sK3)
    | spl8_5
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f107,f126])).

fof(f107,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f191,plain,
    ( spl8_15
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f161,f120,f110,f188])).

fof(f161,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f159,f112])).

fof(f159,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_8 ),
    inference(superposition,[],[f122,f58])).

fof(f122,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f183,plain,
    ( spl8_14
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f134,f124,f115,f180])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f132,f70])).

fof(f132,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f117,f126])).

fof(f167,plain,
    ( spl8_13
    | ~ spl8_4
    | spl8_9 ),
    inference(avatar_split_clause,[],[f150,f124,f96,f164])).

fof(f150,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_4
    | spl8_9 ),
    inference(subsumption_resolution,[],[f103,f125])).

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f102,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_4 ),
    inference(resolution,[],[f98,f66])).

fof(f144,plain,
    ( spl8_11
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f129,f124,f96,f141])).

fof(f129,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f98,f126])).

fof(f139,plain,
    ( spl8_10
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f128,f124,f91,f136])).

fof(f128,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f93,f126])).

fof(f118,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f38,f115])).

fof(f113,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f34,f110])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f35,f105])).

fof(f35,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f37,f96])).

fof(f37,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f33,f91])).

fof(f33,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:32:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (13868)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (13875)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (13867)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (13888)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (13883)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (13871)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.55  % (13880)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.55  % (13892)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.56  % (13884)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (13876)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.56  % (13870)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.61/0.56  % (13875)Refutation not found, incomplete strategy% (13875)------------------------------
% 1.61/0.56  % (13875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.56  % (13875)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.56  
% 1.61/0.56  % (13875)Memory used [KB]: 10746
% 1.61/0.56  % (13875)Time elapsed: 0.146 s
% 1.61/0.56  % (13875)------------------------------
% 1.61/0.56  % (13875)------------------------------
% 1.61/0.56  % (13867)Refutation not found, incomplete strategy% (13867)------------------------------
% 1.61/0.56  % (13867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.56  % (13867)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.56  
% 1.61/0.56  % (13867)Memory used [KB]: 10874
% 1.61/0.56  % (13867)Time elapsed: 0.105 s
% 1.61/0.56  % (13867)------------------------------
% 1.61/0.56  % (13867)------------------------------
% 1.61/0.57  % (13872)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.61/0.57  % (13873)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.61/0.58  % (13865)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.61/0.58  % (13876)Refutation not found, incomplete strategy% (13876)------------------------------
% 1.61/0.58  % (13876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (13876)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (13876)Memory used [KB]: 10746
% 1.61/0.58  % (13876)Time elapsed: 0.163 s
% 1.61/0.58  % (13876)------------------------------
% 1.61/0.58  % (13876)------------------------------
% 1.61/0.59  % (13869)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.61/0.59  % (13891)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.61/0.59  % (13873)Refutation not found, incomplete strategy% (13873)------------------------------
% 1.61/0.59  % (13873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.59  % (13873)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (13873)Memory used [KB]: 10746
% 1.61/0.59  % (13873)Time elapsed: 0.154 s
% 1.61/0.59  % (13873)------------------------------
% 1.61/0.59  % (13873)------------------------------
% 1.61/0.59  % (13894)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.61/0.59  % (13885)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.61/0.60  % (13889)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.61/0.60  % (13886)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.61/0.60  % (13877)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.61/0.60  % (13879)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.61/0.60  % (13866)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.61/0.60  % (13881)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.61/0.61  % (13893)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.61/0.61  % (13878)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.61/0.61  % (13887)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.61/0.62  % (13874)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.61/0.62  % (13890)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.61/0.62  % (13882)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.14/0.64  % (13887)Refutation not found, incomplete strategy% (13887)------------------------------
% 2.14/0.64  % (13887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.64  % (13887)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.64  
% 2.14/0.64  % (13887)Memory used [KB]: 11001
% 2.14/0.64  % (13887)Time elapsed: 0.223 s
% 2.14/0.64  % (13887)------------------------------
% 2.14/0.64  % (13887)------------------------------
% 2.14/0.65  % (13885)Refutation found. Thanks to Tanya!
% 2.14/0.65  % SZS status Theorem for theBenchmark
% 2.14/0.65  % SZS output start Proof for theBenchmark
% 2.14/0.67  fof(f882,plain,(
% 2.14/0.67    $false),
% 2.14/0.67    inference(avatar_sat_refutation,[],[f82,f87,f94,f99,f108,f113,f118,f139,f144,f167,f183,f191,f207,f216,f292,f322,f324,f338,f344,f361,f374,f377,f565,f639,f644,f647,f648,f649,f802,f845,f881])).
% 2.14/0.67  fof(f881,plain,(
% 2.14/0.67    ~spl8_7 | spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_18 | ~spl8_19 | ~spl8_21 | ~spl8_27),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f880])).
% 2.14/0.67  fof(f880,plain,(
% 2.14/0.67    $false | (~spl8_7 | spl8_8 | ~spl8_9 | ~spl8_12 | ~spl8_18 | ~spl8_19 | ~spl8_21 | ~spl8_27)),
% 2.14/0.67    inference(subsumption_resolution,[],[f879,f148])).
% 2.14/0.67  fof(f148,plain,(
% 2.14/0.67    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl8_12),
% 2.14/0.67    inference(avatar_component_clause,[],[f146])).
% 2.14/0.67  fof(f146,plain,(
% 2.14/0.67    spl8_12 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 2.14/0.67  fof(f879,plain,(
% 2.14/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl8_7 | spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_19 | ~spl8_21 | ~spl8_27)),
% 2.14/0.67    inference(forward_demodulation,[],[f878,f70])).
% 2.14/0.67  fof(f70,plain,(
% 2.14/0.67    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.14/0.67    inference(equality_resolution,[],[f56])).
% 2.14/0.67  fof(f56,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f5])).
% 2.14/0.67  fof(f5,axiom,(
% 2.14/0.67    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.14/0.67  fof(f878,plain,(
% 2.14/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_7 | spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_19 | ~spl8_21 | ~spl8_27)),
% 2.14/0.67    inference(subsumption_resolution,[],[f875,f866])).
% 2.14/0.67  fof(f866,plain,(
% 2.14/0.67    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl8_7 | spl8_8 | ~spl8_9 | ~spl8_18 | ~spl8_19 | ~spl8_27)),
% 2.14/0.67    inference(forward_demodulation,[],[f865,f656])).
% 2.14/0.67  fof(f656,plain,(
% 2.14/0.67    k1_xboole_0 = sK0 | (~spl8_7 | ~spl8_18 | ~spl8_19 | ~spl8_27)),
% 2.14/0.67    inference(global_subsumption,[],[f215])).
% 2.14/0.67  fof(f215,plain,(
% 2.14/0.67    k1_xboole_0 = sK0 | ~spl8_18),
% 2.14/0.67    inference(avatar_component_clause,[],[f213])).
% 2.14/0.67  fof(f213,plain,(
% 2.14/0.67    spl8_18 <=> k1_xboole_0 = sK0),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 2.14/0.67  fof(f865,plain,(
% 2.14/0.67    sK0 != k1_relset_1(sK0,k1_xboole_0,sK3) | (spl8_8 | ~spl8_9)),
% 2.14/0.67    inference(forward_demodulation,[],[f121,f126])).
% 2.14/0.67  fof(f126,plain,(
% 2.14/0.67    k1_xboole_0 = sK1 | ~spl8_9),
% 2.14/0.67    inference(avatar_component_clause,[],[f124])).
% 2.14/0.67  fof(f124,plain,(
% 2.14/0.67    spl8_9 <=> k1_xboole_0 = sK1),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.14/0.67  fof(f121,plain,(
% 2.14/0.67    sK0 != k1_relset_1(sK0,sK1,sK3) | spl8_8),
% 2.14/0.67    inference(avatar_component_clause,[],[f120])).
% 2.14/0.67  fof(f120,plain,(
% 2.14/0.67    spl8_8 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.14/0.67  fof(f875,plain,(
% 2.14/0.67    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl8_21),
% 2.14/0.67    inference(resolution,[],[f297,f72])).
% 2.14/0.67  fof(f72,plain,(
% 2.14/0.67    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.14/0.67    inference(equality_resolution,[],[f64])).
% 2.14/0.67  fof(f64,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f28])).
% 2.14/0.67  fof(f28,plain,(
% 2.14/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.67    inference(flattening,[],[f27])).
% 2.14/0.67  fof(f27,plain,(
% 2.14/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.67    inference(ennf_transformation,[],[f14])).
% 2.14/0.67  fof(f14,axiom,(
% 2.14/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.14/0.67  fof(f297,plain,(
% 2.14/0.67    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl8_21),
% 2.14/0.67    inference(avatar_component_clause,[],[f295])).
% 2.14/0.67  fof(f295,plain,(
% 2.14/0.67    spl8_21 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 2.14/0.67  fof(f845,plain,(
% 2.14/0.67    ~spl8_34 | ~spl8_17 | spl8_30),
% 2.14/0.67    inference(avatar_split_clause,[],[f768,f401,f209,f562])).
% 2.14/0.67  fof(f562,plain,(
% 2.14/0.67    spl8_34 <=> k1_xboole_0 = sK2),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 2.14/0.67  fof(f209,plain,(
% 2.14/0.67    spl8_17 <=> k1_xboole_0 = sK3),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 2.14/0.67  fof(f401,plain,(
% 2.14/0.67    spl8_30 <=> sK2 = sK3),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 2.14/0.67  fof(f768,plain,(
% 2.14/0.67    k1_xboole_0 != sK2 | (~spl8_17 | spl8_30)),
% 2.14/0.67    inference(backward_demodulation,[],[f402,f211])).
% 2.14/0.67  fof(f211,plain,(
% 2.14/0.67    k1_xboole_0 = sK3 | ~spl8_17),
% 2.14/0.67    inference(avatar_component_clause,[],[f209])).
% 2.14/0.67  fof(f402,plain,(
% 2.14/0.67    sK2 != sK3 | spl8_30),
% 2.14/0.67    inference(avatar_component_clause,[],[f401])).
% 2.14/0.67  fof(f802,plain,(
% 2.14/0.67    ~spl8_4 | ~spl8_7 | spl8_13 | ~spl8_14 | ~spl8_18 | ~spl8_22),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f801])).
% 2.14/0.67  fof(f801,plain,(
% 2.14/0.67    $false | (~spl8_4 | ~spl8_7 | spl8_13 | ~spl8_14 | ~spl8_18 | ~spl8_22)),
% 2.14/0.67    inference(subsumption_resolution,[],[f800,f182])).
% 2.14/0.67  fof(f182,plain,(
% 2.14/0.67    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl8_14),
% 2.14/0.67    inference(avatar_component_clause,[],[f180])).
% 2.14/0.67  fof(f180,plain,(
% 2.14/0.67    spl8_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 2.14/0.67  fof(f800,plain,(
% 2.14/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl8_4 | ~spl8_7 | spl8_13 | ~spl8_18 | ~spl8_22)),
% 2.14/0.67    inference(forward_demodulation,[],[f799,f70])).
% 2.14/0.67  fof(f799,plain,(
% 2.14/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_4 | ~spl8_7 | spl8_13 | ~spl8_18 | ~spl8_22)),
% 2.14/0.67    inference(subsumption_resolution,[],[f796,f288])).
% 2.14/0.67  fof(f288,plain,(
% 2.14/0.67    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl8_4 | ~spl8_7 | spl8_13 | ~spl8_18)),
% 2.14/0.67    inference(backward_demodulation,[],[f254,f215])).
% 2.14/0.67  fof(f254,plain,(
% 2.14/0.67    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (~spl8_4 | ~spl8_7 | spl8_13)),
% 2.14/0.67    inference(backward_demodulation,[],[f165,f251])).
% 2.14/0.67  fof(f251,plain,(
% 2.14/0.67    k1_xboole_0 = sK1 | (~spl8_4 | ~spl8_7 | spl8_13)),
% 2.14/0.67    inference(subsumption_resolution,[],[f234,f165])).
% 2.14/0.67  fof(f234,plain,(
% 2.14/0.67    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl8_4 | ~spl8_7)),
% 2.14/0.67    inference(subsumption_resolution,[],[f220,f117])).
% 2.14/0.67  fof(f117,plain,(
% 2.14/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_7),
% 2.14/0.67    inference(avatar_component_clause,[],[f115])).
% 2.14/0.67  fof(f115,plain,(
% 2.14/0.67    spl8_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 2.14/0.67  fof(f220,plain,(
% 2.14/0.67    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_4),
% 2.14/0.67    inference(resolution,[],[f98,f66])).
% 2.14/0.67  fof(f66,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.14/0.67    inference(cnf_transformation,[],[f28])).
% 2.14/0.67  fof(f98,plain,(
% 2.14/0.67    v1_funct_2(sK2,sK0,sK1) | ~spl8_4),
% 2.14/0.67    inference(avatar_component_clause,[],[f96])).
% 2.14/0.67  fof(f96,plain,(
% 2.14/0.67    spl8_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.14/0.67  fof(f165,plain,(
% 2.14/0.67    sK0 != k1_relset_1(sK0,sK1,sK2) | spl8_13),
% 2.14/0.67    inference(avatar_component_clause,[],[f164])).
% 2.14/0.67  fof(f164,plain,(
% 2.14/0.67    spl8_13 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 2.14/0.67  fof(f796,plain,(
% 2.14/0.67    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl8_22),
% 2.14/0.67    inference(resolution,[],[f321,f72])).
% 2.14/0.67  fof(f321,plain,(
% 2.14/0.67    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl8_22),
% 2.14/0.67    inference(avatar_component_clause,[],[f319])).
% 2.14/0.67  fof(f319,plain,(
% 2.14/0.67    spl8_22 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 2.14/0.67  fof(f649,plain,(
% 2.14/0.67    k1_xboole_0 != sK1 | r2_relset_1(sK0,k1_xboole_0,sK2,sK2) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 2.14/0.67    introduced(theory_tautology_sat_conflict,[])).
% 2.14/0.67  fof(f648,plain,(
% 2.14/0.67    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 2.14/0.67    introduced(theory_tautology_sat_conflict,[])).
% 2.14/0.67  fof(f647,plain,(
% 2.14/0.67    ~spl8_7 | spl8_37),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f646])).
% 2.14/0.67  fof(f646,plain,(
% 2.14/0.67    $false | (~spl8_7 | spl8_37)),
% 2.14/0.67    inference(subsumption_resolution,[],[f645,f117])).
% 2.14/0.67  fof(f645,plain,(
% 2.14/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl8_37),
% 2.14/0.67    inference(resolution,[],[f637,f77])).
% 2.14/0.67  fof(f77,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (r2_relset_1(X1,X2,X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 2.14/0.67    inference(condensation,[],[f67])).
% 2.14/0.67  fof(f67,plain,(
% 2.14/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f30])).
% 2.14/0.67  fof(f30,plain,(
% 2.14/0.67    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.67    inference(flattening,[],[f29])).
% 2.14/0.67  fof(f29,plain,(
% 2.14/0.67    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.14/0.67    inference(ennf_transformation,[],[f13])).
% 2.14/0.67  fof(f13,axiom,(
% 2.14/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 2.14/0.67  fof(f637,plain,(
% 2.14/0.67    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl8_37),
% 2.14/0.67    inference(avatar_component_clause,[],[f635])).
% 2.14/0.67  fof(f635,plain,(
% 2.14/0.67    spl8_37 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 2.14/0.67  fof(f644,plain,(
% 2.14/0.67    ~spl8_38 | ~spl8_1 | ~spl8_2 | ~spl8_15 | spl8_16 | ~spl8_19 | ~spl8_24 | ~spl8_27 | ~spl8_28),
% 2.14/0.67    inference(avatar_split_clause,[],[f618,f372,f368,f348,f229,f204,f188,f84,f79,f641])).
% 2.14/0.67  fof(f641,plain,(
% 2.14/0.67    spl8_38 <=> r2_relset_1(sK0,k1_xboole_0,sK2,sK2)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 2.14/0.67  fof(f79,plain,(
% 2.14/0.67    spl8_1 <=> v1_funct_1(sK3)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.14/0.67  fof(f84,plain,(
% 2.14/0.67    spl8_2 <=> v1_funct_1(sK2)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.14/0.67  fof(f188,plain,(
% 2.14/0.67    spl8_15 <=> sK0 = k1_relat_1(sK3)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 2.14/0.67  fof(f204,plain,(
% 2.14/0.67    spl8_16 <=> r2_relset_1(sK0,k1_xboole_0,sK2,sK3)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 2.14/0.67  fof(f229,plain,(
% 2.14/0.67    spl8_19 <=> sK0 = k1_relat_1(sK2)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 2.14/0.67  fof(f348,plain,(
% 2.14/0.67    spl8_24 <=> v1_relat_1(sK3)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 2.14/0.67  fof(f368,plain,(
% 2.14/0.67    spl8_27 <=> v1_relat_1(sK2)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 2.14/0.67  fof(f372,plain,(
% 2.14/0.67    spl8_28 <=> ! [X0] : (k1_relat_1(X0) != sK0 | sK2 = X0 | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 2.14/0.67  fof(f618,plain,(
% 2.14/0.67    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK2) | (~spl8_1 | ~spl8_2 | ~spl8_15 | spl8_16 | ~spl8_19 | ~spl8_24 | ~spl8_27 | ~spl8_28)),
% 2.14/0.67    inference(backward_demodulation,[],[f206,f609])).
% 2.14/0.67  fof(f609,plain,(
% 2.14/0.67    sK2 = sK3 | (~spl8_1 | ~spl8_2 | ~spl8_15 | ~spl8_19 | ~spl8_24 | ~spl8_27 | ~spl8_28)),
% 2.14/0.67    inference(subsumption_resolution,[],[f608,f349])).
% 2.14/0.67  fof(f349,plain,(
% 2.14/0.67    v1_relat_1(sK3) | ~spl8_24),
% 2.14/0.67    inference(avatar_component_clause,[],[f348])).
% 2.14/0.67  fof(f608,plain,(
% 2.14/0.67    sK2 = sK3 | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_2 | ~spl8_15 | ~spl8_19 | ~spl8_27 | ~spl8_28)),
% 2.14/0.67    inference(subsumption_resolution,[],[f607,f81])).
% 2.14/0.67  fof(f81,plain,(
% 2.14/0.67    v1_funct_1(sK3) | ~spl8_1),
% 2.14/0.67    inference(avatar_component_clause,[],[f79])).
% 2.14/0.67  fof(f607,plain,(
% 2.14/0.67    sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_2 | ~spl8_15 | ~spl8_19 | ~spl8_27 | ~spl8_28)),
% 2.14/0.67    inference(subsumption_resolution,[],[f606,f190])).
% 2.14/0.67  fof(f190,plain,(
% 2.14/0.67    sK0 = k1_relat_1(sK3) | ~spl8_15),
% 2.14/0.67    inference(avatar_component_clause,[],[f188])).
% 2.14/0.67  fof(f606,plain,(
% 2.14/0.67    sK2 = sK3 | sK0 != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_2 | ~spl8_19 | ~spl8_27 | ~spl8_28)),
% 2.14/0.67    inference(trivial_inequality_removal,[],[f605])).
% 2.14/0.67  fof(f605,plain,(
% 2.14/0.67    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | sK0 != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl8_2 | ~spl8_19 | ~spl8_27 | ~spl8_28)),
% 2.14/0.67    inference(duplicate_literal_removal,[],[f604])).
% 2.14/0.67  fof(f604,plain,(
% 2.14/0.67    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | sK0 != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK0 != k1_relat_1(sK3) | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl8_2 | ~spl8_19 | ~spl8_27 | ~spl8_28)),
% 2.14/0.67    inference(superposition,[],[f373,f587])).
% 2.14/0.67  fof(f587,plain,(
% 2.14/0.67    ( ! [X0] : (k1_funct_1(sK2,sK4(sK2,X0)) = k1_funct_1(sK3,sK4(sK2,X0)) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK2 = X0 | ~v1_relat_1(X0)) ) | (~spl8_2 | ~spl8_19 | ~spl8_27)),
% 2.14/0.67    inference(resolution,[],[f538,f31])).
% 2.14/0.67  fof(f31,plain,(
% 2.14/0.67    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f18])).
% 2.14/0.67  fof(f18,plain,(
% 2.14/0.67    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.14/0.67    inference(flattening,[],[f17])).
% 2.14/0.67  fof(f17,plain,(
% 2.14/0.67    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.14/0.67    inference(ennf_transformation,[],[f16])).
% 2.14/0.67  fof(f16,negated_conjecture,(
% 2.14/0.67    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.14/0.67    inference(negated_conjecture,[],[f15])).
% 2.14/0.67  fof(f15,conjecture,(
% 2.14/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 2.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 2.14/0.67  fof(f538,plain,(
% 2.14/0.67    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK2 = X0) ) | (~spl8_2 | ~spl8_19 | ~spl8_27)),
% 2.14/0.67    inference(subsumption_resolution,[],[f537,f369])).
% 2.14/0.67  fof(f369,plain,(
% 2.14/0.67    v1_relat_1(sK2) | ~spl8_27),
% 2.14/0.67    inference(avatar_component_clause,[],[f368])).
% 2.14/0.67  fof(f537,plain,(
% 2.14/0.67    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | sK2 = X0) ) | (~spl8_2 | ~spl8_19)),
% 2.14/0.67    inference(subsumption_resolution,[],[f536,f86])).
% 2.14/0.67  fof(f86,plain,(
% 2.14/0.67    v1_funct_1(sK2) | ~spl8_2),
% 2.14/0.67    inference(avatar_component_clause,[],[f84])).
% 2.14/0.67  fof(f536,plain,(
% 2.14/0.67    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | sK2 = X0) ) | ~spl8_19),
% 2.14/0.67    inference(superposition,[],[f41,f231])).
% 2.14/0.67  fof(f231,plain,(
% 2.14/0.67    sK0 = k1_relat_1(sK2) | ~spl8_19),
% 2.14/0.67    inference(avatar_component_clause,[],[f229])).
% 2.14/0.67  fof(f41,plain,(
% 2.14/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0) | X0 = X1) )),
% 2.14/0.67    inference(cnf_transformation,[],[f21])).
% 2.14/0.67  fof(f21,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.67    inference(flattening,[],[f20])).
% 2.14/0.67  fof(f20,plain,(
% 2.14/0.67    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.67    inference(ennf_transformation,[],[f9])).
% 2.14/0.67  fof(f9,axiom,(
% 2.14/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 2.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 2.14/0.67  fof(f373,plain,(
% 2.14/0.67    ( ! [X0] : (k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl8_28),
% 2.14/0.67    inference(avatar_component_clause,[],[f372])).
% 2.14/0.67  fof(f206,plain,(
% 2.14/0.67    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3) | spl8_16),
% 2.14/0.67    inference(avatar_component_clause,[],[f204])).
% 2.14/0.67  fof(f639,plain,(
% 2.14/0.67    spl8_30 | ~spl8_1 | ~spl8_2 | ~spl8_15 | ~spl8_19 | ~spl8_24 | ~spl8_27 | ~spl8_28),
% 2.14/0.67    inference(avatar_split_clause,[],[f609,f372,f368,f348,f229,f188,f84,f79,f401])).
% 2.14/0.67  fof(f565,plain,(
% 2.14/0.67    spl8_34 | ~spl8_14 | ~spl8_11 | spl8_18),
% 2.14/0.67    inference(avatar_split_clause,[],[f498,f213,f141,f180,f562])).
% 2.14/0.67  fof(f141,plain,(
% 2.14/0.67    spl8_11 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 2.14/0.67  fof(f498,plain,(
% 2.14/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2 | (~spl8_11 | spl8_18)),
% 2.14/0.67    inference(forward_demodulation,[],[f497,f70])).
% 2.14/0.67  fof(f497,plain,(
% 2.14/0.67    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_11 | spl8_18)),
% 2.14/0.67    inference(subsumption_resolution,[],[f495,f214])).
% 2.14/0.67  fof(f214,plain,(
% 2.14/0.67    k1_xboole_0 != sK0 | spl8_18),
% 2.14/0.67    inference(avatar_component_clause,[],[f213])).
% 2.14/0.67  fof(f495,plain,(
% 2.14/0.67    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_11),
% 2.14/0.67    inference(resolution,[],[f143,f74])).
% 2.14/0.67  fof(f74,plain,(
% 2.14/0.67    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.14/0.67    inference(equality_resolution,[],[f62])).
% 2.14/0.67  fof(f62,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 2.14/0.67    inference(cnf_transformation,[],[f28])).
% 2.14/0.67  fof(f143,plain,(
% 2.14/0.67    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl8_11),
% 2.14/0.67    inference(avatar_component_clause,[],[f141])).
% 2.14/0.67  fof(f377,plain,(
% 2.14/0.67    ~spl8_7 | spl8_27),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f376])).
% 2.14/0.67  fof(f376,plain,(
% 2.14/0.67    $false | (~spl8_7 | spl8_27)),
% 2.14/0.67    inference(subsumption_resolution,[],[f117,f375])).
% 2.14/0.67  fof(f375,plain,(
% 2.14/0.67    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl8_27),
% 2.14/0.67    inference(resolution,[],[f370,f57])).
% 2.14/0.67  fof(f57,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.14/0.67    inference(cnf_transformation,[],[f24])).
% 2.14/0.67  fof(f24,plain,(
% 2.14/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.67    inference(ennf_transformation,[],[f10])).
% 2.14/0.67  fof(f10,axiom,(
% 2.14/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.14/0.67  fof(f370,plain,(
% 2.14/0.67    ~v1_relat_1(sK2) | spl8_27),
% 2.14/0.67    inference(avatar_component_clause,[],[f368])).
% 2.14/0.67  fof(f374,plain,(
% 2.14/0.67    ~spl8_27 | spl8_28 | ~spl8_2 | ~spl8_7 | ~spl8_13),
% 2.14/0.67    inference(avatar_split_clause,[],[f331,f164,f115,f84,f372,f368])).
% 2.14/0.67  fof(f331,plain,(
% 2.14/0.67    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | sK2 = X0) ) | (~spl8_2 | ~spl8_7 | ~spl8_13)),
% 2.14/0.67    inference(forward_demodulation,[],[f89,f226])).
% 2.14/0.67  fof(f226,plain,(
% 2.14/0.67    sK0 = k1_relat_1(sK2) | (~spl8_7 | ~spl8_13)),
% 2.14/0.67    inference(subsumption_resolution,[],[f224,f117])).
% 2.14/0.67  fof(f224,plain,(
% 2.14/0.67    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_13),
% 2.14/0.67    inference(superposition,[],[f166,f58])).
% 2.14/0.67  fof(f58,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.14/0.67    inference(cnf_transformation,[],[f25])).
% 2.14/0.67  fof(f25,plain,(
% 2.14/0.67    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.67    inference(ennf_transformation,[],[f12])).
% 2.14/0.67  fof(f12,axiom,(
% 2.14/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.14/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.14/0.67  fof(f166,plain,(
% 2.14/0.67    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_13),
% 2.14/0.67    inference(avatar_component_clause,[],[f164])).
% 2.14/0.67  fof(f89,plain,(
% 2.14/0.67    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | sK2 = X0) ) | ~spl8_2),
% 2.14/0.67    inference(resolution,[],[f86,f42])).
% 2.14/0.67  fof(f42,plain,(
% 2.14/0.67    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(X0) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 2.14/0.67    inference(cnf_transformation,[],[f21])).
% 2.14/0.67  fof(f361,plain,(
% 2.14/0.67    ~spl8_6 | spl8_24),
% 2.14/0.67    inference(avatar_contradiction_clause,[],[f360])).
% 2.14/0.67  fof(f360,plain,(
% 2.14/0.67    $false | (~spl8_6 | spl8_24)),
% 2.14/0.67    inference(subsumption_resolution,[],[f112,f359])).
% 2.14/0.67  fof(f359,plain,(
% 2.14/0.67    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl8_24),
% 2.14/0.67    inference(resolution,[],[f350,f57])).
% 2.14/0.67  fof(f350,plain,(
% 2.14/0.67    ~v1_relat_1(sK3) | spl8_24),
% 2.14/0.67    inference(avatar_component_clause,[],[f348])).
% 2.14/0.67  fof(f112,plain,(
% 2.14/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_6),
% 2.14/0.67    inference(avatar_component_clause,[],[f110])).
% 2.14/0.67  fof(f110,plain,(
% 2.14/0.67    spl8_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 2.14/0.67  fof(f344,plain,(
% 2.14/0.67    spl8_8 | ~spl8_3 | ~spl8_6 | spl8_9),
% 2.14/0.67    inference(avatar_split_clause,[],[f218,f124,f110,f91,f120])).
% 2.14/0.67  fof(f91,plain,(
% 2.14/0.67    spl8_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.14/0.67  fof(f218,plain,(
% 2.14/0.67    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl8_3 | ~spl8_6 | spl8_9)),
% 2.14/0.67    inference(subsumption_resolution,[],[f192,f125])).
% 2.14/0.67  fof(f125,plain,(
% 2.14/0.67    k1_xboole_0 != sK1 | spl8_9),
% 2.14/0.67    inference(avatar_component_clause,[],[f124])).
% 2.14/0.67  fof(f192,plain,(
% 2.14/0.67    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl8_3 | ~spl8_6)),
% 2.14/0.67    inference(subsumption_resolution,[],[f185,f112])).
% 2.14/0.67  fof(f185,plain,(
% 2.14/0.67    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 2.14/0.67    inference(resolution,[],[f93,f66])).
% 2.14/0.67  fof(f93,plain,(
% 2.14/0.67    v1_funct_2(sK3,sK0,sK1) | ~spl8_3),
% 2.14/0.67    inference(avatar_component_clause,[],[f91])).
% 2.14/0.67  fof(f338,plain,(
% 2.14/0.67    spl8_19 | ~spl8_7 | ~spl8_13),
% 2.14/0.67    inference(avatar_split_clause,[],[f226,f164,f115,f229])).
% 2.14/0.67  fof(f324,plain,(
% 2.14/0.67    spl8_21 | ~spl8_10 | ~spl8_18),
% 2.14/0.67    inference(avatar_split_clause,[],[f300,f213,f136,f295])).
% 2.14/0.67  fof(f136,plain,(
% 2.14/0.67    spl8_10 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 2.14/0.67  fof(f300,plain,(
% 2.14/0.67    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl8_10 | ~spl8_18)),
% 2.14/0.67    inference(forward_demodulation,[],[f138,f215])).
% 2.14/0.67  fof(f138,plain,(
% 2.14/0.67    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl8_10),
% 2.14/0.67    inference(avatar_component_clause,[],[f136])).
% 2.14/0.67  fof(f322,plain,(
% 2.14/0.67    spl8_22 | ~spl8_11 | ~spl8_18),
% 2.14/0.67    inference(avatar_split_clause,[],[f283,f213,f141,f319])).
% 2.14/0.67  fof(f283,plain,(
% 2.14/0.67    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl8_11 | ~spl8_18)),
% 2.14/0.67    inference(backward_demodulation,[],[f143,f215])).
% 2.14/0.67  fof(f292,plain,(
% 2.14/0.67    spl8_12 | ~spl8_6 | ~spl8_9),
% 2.14/0.67    inference(avatar_split_clause,[],[f133,f124,f110,f146])).
% 2.14/0.67  fof(f133,plain,(
% 2.14/0.67    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl8_6 | ~spl8_9)),
% 2.14/0.67    inference(forward_demodulation,[],[f131,f70])).
% 2.14/0.67  fof(f131,plain,(
% 2.14/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_6 | ~spl8_9)),
% 2.14/0.67    inference(backward_demodulation,[],[f112,f126])).
% 2.14/0.67  fof(f216,plain,(
% 2.14/0.67    spl8_17 | spl8_18 | ~spl8_10 | ~spl8_12),
% 2.14/0.67    inference(avatar_split_clause,[],[f169,f146,f136,f213,f209])).
% 2.14/0.67  fof(f169,plain,(
% 2.14/0.67    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | (~spl8_10 | ~spl8_12)),
% 2.14/0.67    inference(subsumption_resolution,[],[f155,f148])).
% 2.14/0.67  fof(f155,plain,(
% 2.14/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl8_10),
% 2.14/0.67    inference(forward_demodulation,[],[f153,f70])).
% 2.14/0.67  fof(f153,plain,(
% 2.14/0.67    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_10),
% 2.14/0.67    inference(resolution,[],[f138,f74])).
% 2.14/0.67  fof(f207,plain,(
% 2.14/0.67    ~spl8_16 | spl8_5 | ~spl8_9),
% 2.14/0.67    inference(avatar_split_clause,[],[f130,f124,f105,f204])).
% 2.14/0.67  fof(f105,plain,(
% 2.14/0.67    spl8_5 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 2.14/0.67    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.14/0.67  fof(f130,plain,(
% 2.14/0.67    ~r2_relset_1(sK0,k1_xboole_0,sK2,sK3) | (spl8_5 | ~spl8_9)),
% 2.14/0.67    inference(backward_demodulation,[],[f107,f126])).
% 2.14/0.67  fof(f107,plain,(
% 2.14/0.67    ~r2_relset_1(sK0,sK1,sK2,sK3) | spl8_5),
% 2.14/0.67    inference(avatar_component_clause,[],[f105])).
% 2.14/0.67  fof(f191,plain,(
% 2.14/0.67    spl8_15 | ~spl8_6 | ~spl8_8),
% 2.14/0.67    inference(avatar_split_clause,[],[f161,f120,f110,f188])).
% 2.14/0.67  fof(f161,plain,(
% 2.14/0.67    sK0 = k1_relat_1(sK3) | (~spl8_6 | ~spl8_8)),
% 2.14/0.67    inference(subsumption_resolution,[],[f159,f112])).
% 2.14/0.67  fof(f159,plain,(
% 2.14/0.67    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_8),
% 2.14/0.67    inference(superposition,[],[f122,f58])).
% 2.14/0.67  fof(f122,plain,(
% 2.14/0.67    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_8),
% 2.14/0.67    inference(avatar_component_clause,[],[f120])).
% 2.14/0.67  fof(f183,plain,(
% 2.14/0.67    spl8_14 | ~spl8_7 | ~spl8_9),
% 2.14/0.67    inference(avatar_split_clause,[],[f134,f124,f115,f180])).
% 2.14/0.67  fof(f134,plain,(
% 2.14/0.67    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl8_7 | ~spl8_9)),
% 2.14/0.67    inference(forward_demodulation,[],[f132,f70])).
% 2.14/0.67  fof(f132,plain,(
% 2.14/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_7 | ~spl8_9)),
% 2.14/0.67    inference(backward_demodulation,[],[f117,f126])).
% 2.14/0.67  fof(f167,plain,(
% 2.14/0.67    spl8_13 | ~spl8_4 | spl8_9),
% 2.14/0.67    inference(avatar_split_clause,[],[f150,f124,f96,f164])).
% 2.14/0.67  fof(f150,plain,(
% 2.14/0.67    sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl8_4 | spl8_9)),
% 2.14/0.67    inference(subsumption_resolution,[],[f103,f125])).
% 2.14/0.67  fof(f103,plain,(
% 2.14/0.67    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_4),
% 2.14/0.67    inference(subsumption_resolution,[],[f102,f38])).
% 2.14/0.67  fof(f38,plain,(
% 2.14/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.14/0.67    inference(cnf_transformation,[],[f18])).
% 2.14/0.67  fof(f102,plain,(
% 2.14/0.67    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_4),
% 2.14/0.67    inference(resolution,[],[f98,f66])).
% 2.14/0.67  fof(f144,plain,(
% 2.14/0.67    spl8_11 | ~spl8_4 | ~spl8_9),
% 2.14/0.67    inference(avatar_split_clause,[],[f129,f124,f96,f141])).
% 2.14/0.67  fof(f129,plain,(
% 2.14/0.67    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl8_4 | ~spl8_9)),
% 2.14/0.67    inference(backward_demodulation,[],[f98,f126])).
% 2.14/0.67  fof(f139,plain,(
% 2.14/0.67    spl8_10 | ~spl8_3 | ~spl8_9),
% 2.14/0.67    inference(avatar_split_clause,[],[f128,f124,f91,f136])).
% 2.14/0.67  fof(f128,plain,(
% 2.14/0.67    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl8_3 | ~spl8_9)),
% 2.14/0.67    inference(backward_demodulation,[],[f93,f126])).
% 2.14/0.67  fof(f118,plain,(
% 2.14/0.67    spl8_7),
% 2.14/0.67    inference(avatar_split_clause,[],[f38,f115])).
% 2.14/0.67  fof(f113,plain,(
% 2.14/0.67    spl8_6),
% 2.14/0.67    inference(avatar_split_clause,[],[f34,f110])).
% 2.14/0.67  fof(f34,plain,(
% 2.14/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.14/0.67    inference(cnf_transformation,[],[f18])).
% 2.14/0.67  fof(f108,plain,(
% 2.14/0.67    ~spl8_5),
% 2.14/0.67    inference(avatar_split_clause,[],[f35,f105])).
% 2.14/0.67  fof(f35,plain,(
% 2.14/0.67    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 2.14/0.67    inference(cnf_transformation,[],[f18])).
% 2.14/0.67  fof(f99,plain,(
% 2.14/0.67    spl8_4),
% 2.14/0.67    inference(avatar_split_clause,[],[f37,f96])).
% 2.14/0.67  fof(f37,plain,(
% 2.14/0.67    v1_funct_2(sK2,sK0,sK1)),
% 2.14/0.67    inference(cnf_transformation,[],[f18])).
% 2.14/0.67  fof(f94,plain,(
% 2.14/0.67    spl8_3),
% 2.14/0.67    inference(avatar_split_clause,[],[f33,f91])).
% 2.14/0.67  fof(f33,plain,(
% 2.14/0.67    v1_funct_2(sK3,sK0,sK1)),
% 2.14/0.67    inference(cnf_transformation,[],[f18])).
% 2.14/0.67  fof(f87,plain,(
% 2.14/0.67    spl8_2),
% 2.14/0.67    inference(avatar_split_clause,[],[f36,f84])).
% 2.14/0.67  fof(f36,plain,(
% 2.14/0.67    v1_funct_1(sK2)),
% 2.14/0.67    inference(cnf_transformation,[],[f18])).
% 2.14/0.67  fof(f82,plain,(
% 2.14/0.67    spl8_1),
% 2.14/0.67    inference(avatar_split_clause,[],[f32,f79])).
% 2.14/0.67  fof(f32,plain,(
% 2.14/0.67    v1_funct_1(sK3)),
% 2.14/0.67    inference(cnf_transformation,[],[f18])).
% 2.14/0.67  % SZS output end Proof for theBenchmark
% 2.14/0.67  % (13885)------------------------------
% 2.14/0.67  % (13885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (13885)Termination reason: Refutation
% 2.14/0.67  
% 2.14/0.67  % (13885)Memory used [KB]: 11257
% 2.14/0.67  % (13885)Time elapsed: 0.215 s
% 2.14/0.67  % (13885)------------------------------
% 2.14/0.67  % (13885)------------------------------
% 2.14/0.67  % (13864)Success in time 0.313 s
%------------------------------------------------------------------------------
