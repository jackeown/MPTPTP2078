%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t17_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:38 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 330 expanded)
%              Number of leaves         :   42 ( 144 expanded)
%              Depth                    :    9
%              Number of atoms          :  492 ( 930 expanded)
%              Number of equality atoms :   80 ( 182 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2915,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f96,f100,f104,f128,f134,f142,f148,f152,f170,f182,f197,f219,f275,f304,f312,f350,f365,f542,f650,f681,f825,f827,f1095,f1176,f2671,f2905,f2913,f2914])).

fof(f2914,plain,
    ( k1_xboole_0 != sK3
    | r2_hidden(sK6(sK3,sK2),sK0)
    | ~ r2_hidden(sK6(k1_xboole_0,sK2),sK0) ),
    introduced(theory_axiom,[])).

fof(f2913,plain,
    ( ~ spl8_63
    | ~ spl8_204
    | ~ spl8_222 ),
    inference(avatar_split_clause,[],[f2117,f1174,f1093,f285])).

fof(f285,plain,
    ( spl8_63
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f1093,plain,
    ( spl8_204
  <=> m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_204])])).

fof(f1174,plain,
    ( spl8_222
  <=> r2_hidden(sK6(k1_xboole_0,sK2),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_222])])).

fof(f2117,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_204
    | ~ spl8_222 ),
    inference(resolution,[],[f1233,f1094])).

fof(f1094,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl8_204 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f1233,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl8_222 ),
    inference(resolution,[],[f1175,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',t5_subset)).

fof(f1175,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK2),k1_relat_1(k1_xboole_0))
    | ~ spl8_222 ),
    inference(avatar_component_clause,[],[f1174])).

fof(f2905,plain,
    ( spl8_296
    | spl8_63
    | ~ spl8_292 ),
    inference(avatar_split_clause,[],[f2887,f2669,f285,f2903])).

fof(f2903,plain,
    ( spl8_296
  <=> r2_hidden(sK6(k1_xboole_0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_296])])).

fof(f2669,plain,
    ( spl8_292
  <=> m1_subset_1(sK6(k1_xboole_0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_292])])).

fof(f2887,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK2),sK0)
    | ~ spl8_63
    | ~ spl8_292 ),
    inference(subsumption_resolution,[],[f2886,f286])).

fof(f286,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f285])).

fof(f2886,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK6(k1_xboole_0,sK2),sK0)
    | ~ spl8_292 ),
    inference(resolution,[],[f2670,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',t2_subset)).

fof(f2670,plain,
    ( m1_subset_1(sK6(k1_xboole_0,sK2),sK0)
    | ~ spl8_292 ),
    inference(avatar_component_clause,[],[f2669])).

fof(f2671,plain,
    ( spl8_292
    | ~ spl8_16
    | ~ spl8_26
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f2640,f537,f180,f146,f2669])).

fof(f146,plain,
    ( spl8_16
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f180,plain,
    ( spl8_26
  <=> r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f537,plain,
    ( spl8_120
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).

fof(f2640,plain,
    ( m1_subset_1(sK6(k1_xboole_0,sK2),sK0)
    | ~ spl8_16
    | ~ spl8_26
    | ~ spl8_120 ),
    inference(forward_demodulation,[],[f2637,f538])).

fof(f538,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_120 ),
    inference(avatar_component_clause,[],[f537])).

fof(f2637,plain,
    ( m1_subset_1(sK6(sK3,sK2),sK0)
    | ~ spl8_16
    | ~ spl8_26 ),
    inference(resolution,[],[f191,f147])).

fof(f147,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X0))
        | m1_subset_1(sK6(sK3,sK2),X0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f181,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',t4_subset)).

fof(f181,plain,
    ( r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f180])).

fof(f1176,plain,
    ( spl8_222
    | ~ spl8_26
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f570,f537,f180,f1174])).

fof(f570,plain,
    ( r2_hidden(sK6(k1_xboole_0,sK2),k1_relat_1(k1_xboole_0))
    | ~ spl8_26
    | ~ spl8_120 ),
    inference(superposition,[],[f181,f538])).

fof(f1095,plain,
    ( spl8_204
    | ~ spl8_16
    | ~ spl8_120 ),
    inference(avatar_split_clause,[],[f867,f537,f146,f1093])).

fof(f867,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl8_16
    | ~ spl8_120 ),
    inference(superposition,[],[f147,f538])).

fof(f827,plain,
    ( k1_xboole_0 != sK1
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_xboole_0 != sK0
    | r2_hidden(sK6(sK3,sK2),sK0)
    | ~ r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(theory_axiom,[])).

fof(f825,plain,
    ( spl8_162
    | ~ spl8_134
    | ~ spl8_142 ),
    inference(avatar_split_clause,[],[f737,f679,f648,f823])).

fof(f823,plain,
    ( spl8_162
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_162])])).

fof(f648,plain,
    ( spl8_134
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f679,plain,
    ( spl8_142
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f737,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl8_134
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f726,f649])).

fof(f649,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_134 ),
    inference(avatar_component_clause,[],[f648])).

fof(f726,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_142 ),
    inference(resolution,[],[f680,f84])).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',d1_funct_2)).

fof(f680,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_142 ),
    inference(avatar_component_clause,[],[f679])).

fof(f681,plain,
    ( spl8_142
    | ~ spl8_4
    | ~ spl8_40
    | ~ spl8_122 ),
    inference(avatar_split_clause,[],[f637,f540,f217,f98,f679])).

fof(f98,plain,
    ( spl8_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f217,plain,
    ( spl8_40
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f540,plain,
    ( spl8_122
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f637,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_40
    | ~ spl8_122 ),
    inference(forward_demodulation,[],[f614,f218])).

fof(f218,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f217])).

fof(f614,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl8_4
    | ~ spl8_122 ),
    inference(superposition,[],[f99,f541])).

fof(f541,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_122 ),
    inference(avatar_component_clause,[],[f540])).

fof(f99,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f650,plain,
    ( spl8_134
    | ~ spl8_2
    | ~ spl8_40
    | ~ spl8_122 ),
    inference(avatar_split_clause,[],[f636,f540,f217,f94,f648])).

fof(f94,plain,
    ( spl8_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f636,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_40
    | ~ spl8_122 ),
    inference(forward_demodulation,[],[f613,f218])).

fof(f613,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl8_2
    | ~ spl8_122 ),
    inference(superposition,[],[f95,f541])).

fof(f95,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f542,plain,
    ( spl8_120
    | spl8_122
    | ~ spl8_74
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f379,f363,f348,f540,f537])).

fof(f348,plain,
    ( spl8_74
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f363,plain,
    ( spl8_80
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f379,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl8_74
    | ~ spl8_80 ),
    inference(subsumption_resolution,[],[f370,f349])).

fof(f349,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f348])).

fof(f370,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_80 ),
    inference(resolution,[],[f364,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f364,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f363])).

fof(f365,plain,
    ( spl8_80
    | ~ spl8_4
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f227,f217,f98,f363])).

fof(f227,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_4
    | ~ spl8_40 ),
    inference(superposition,[],[f99,f218])).

fof(f350,plain,
    ( spl8_74
    | ~ spl8_2
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f226,f217,f94,f348])).

fof(f226,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_40 ),
    inference(superposition,[],[f95,f218])).

fof(f312,plain,
    ( ~ spl8_22
    | ~ spl8_68 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl8_22
    | ~ spl8_68 ),
    inference(subsumption_resolution,[],[f305,f176])).

fof(f176,plain,
    ( k1_funct_1(sK3,sK6(sK3,sK2)) = sK2
    | ~ spl8_22 ),
    inference(resolution,[],[f169,f57])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | k1_funct_1(X0,sK6(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',d5_funct_1)).

fof(f169,plain,
    ( sP5(sK2,sK3)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl8_22
  <=> sP5(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f305,plain,
    ( k1_funct_1(sK3,sK6(sK3,sK2)) != sK2
    | ~ spl8_68 ),
    inference(resolution,[],[f303,f49])).

fof(f49,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK3,X4) != sK2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',t17_funct_2)).

fof(f303,plain,
    ( r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl8_68
  <=> r2_hidden(sK6(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f304,plain,
    ( spl8_68
    | ~ spl8_26
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f281,f255,f180,f302])).

fof(f255,plain,
    ( spl8_56
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f281,plain,
    ( r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl8_26
    | ~ spl8_56 ),
    inference(superposition,[],[f181,f256])).

fof(f256,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f255])).

fof(f275,plain,
    ( spl8_56
    | ~ spl8_30
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f259,f214,f195,f255])).

fof(f195,plain,
    ( spl8_30
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f214,plain,
    ( spl8_38
  <=> k1_relset_1(sK0,sK1,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f259,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl8_30
    | ~ spl8_38 ),
    inference(superposition,[],[f215,f196])).

fof(f196,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f195])).

fof(f215,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f214])).

fof(f219,plain,
    ( spl8_38
    | spl8_40
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f113,f98,f94,f217,f214])).

fof(f113,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f108,f95])).

fof(f108,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f99,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f197,plain,
    ( spl8_30
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f109,f98,f195])).

fof(f109,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f99,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',redefinition_k1_relset_1)).

fof(f182,plain,
    ( spl8_26
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f175,f168,f180])).

fof(f175,plain,
    ( r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))
    | ~ spl8_22 ),
    inference(resolution,[],[f169,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | r2_hidden(sK6(X0,X2),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f170,plain,
    ( spl8_22
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f161,f150,f126,f90,f168])).

fof(f90,plain,
    ( spl8_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f126,plain,
    ( spl8_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f150,plain,
    ( spl8_18
  <=> r2_hidden(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f161,plain,
    ( sP5(sK2,sK3)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f160,f127])).

fof(f127,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f160,plain,
    ( sP5(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_0
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f154,f91])).

fof(f91,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f90])).

fof(f154,plain,
    ( ~ v1_funct_1(sK3)
    | sP5(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_18 ),
    inference(resolution,[],[f151,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP5(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f151,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( spl8_18
    | spl8_11
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f144,f140,f132,f150])).

fof(f132,plain,
    ( spl8_11
  <=> ~ v1_xboole_0(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f140,plain,
    ( spl8_14
  <=> m1_subset_1(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f144,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f143,f133])).

fof(f133,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f143,plain,
    ( v1_xboole_0(k2_relat_1(sK3))
    | r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl8_14 ),
    inference(resolution,[],[f141,f65])).

fof(f141,plain,
    ( m1_subset_1(sK2,k2_relat_1(sK3))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f148,plain,
    ( spl8_16
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f114,f98,f146])).

fof(f114,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f111,f109])).

fof(f111,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0))
    | ~ spl8_4 ),
    inference(resolution,[],[f99,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',dt_k1_relset_1)).

fof(f142,plain,
    ( spl8_14
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f121,f102,f98,f140])).

fof(f102,plain,
    ( spl8_6
  <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f121,plain,
    ( m1_subset_1(sK2,k2_relat_1(sK3))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f116,f106])).

fof(f106,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f99,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',redefinition_k2_relset_1)).

fof(f116,plain,
    ( m1_subset_1(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ spl8_6 ),
    inference(resolution,[],[f103,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',t1_subset)).

fof(f103,plain,
    ( r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f134,plain,
    ( ~ spl8_11
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f122,f102,f98,f132])).

fof(f122,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f117,f106])).

fof(f117,plain,
    ( ~ v1_xboole_0(k2_relset_1(sK0,sK1,sK3))
    | ~ spl8_6 ),
    inference(resolution,[],[f103,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',t7_boole)).

fof(f128,plain,
    ( spl8_8
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f110,f98,f126])).

fof(f110,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f99,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t17_funct_2.p',cc1_relset_1)).

fof(f104,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f52,f98])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f51,f94])).

fof(f51,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f50,f90])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
