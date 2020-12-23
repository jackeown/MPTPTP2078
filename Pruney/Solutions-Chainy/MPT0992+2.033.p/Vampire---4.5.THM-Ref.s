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
% DateTime   : Thu Dec  3 13:03:14 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 401 expanded)
%              Number of leaves         :   51 ( 172 expanded)
%              Depth                    :    8
%              Number of atoms          :  580 (1186 expanded)
%              Number of equality atoms :  100 ( 238 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1686,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f111,f124,f136,f149,f162,f271,f297,f442,f497,f527,f580,f600,f661,f681,f697,f702,f704,f713,f720,f737,f797,f822,f844,f849,f912,f1234,f1294,f1347,f1446,f1652,f1658])).

fof(f1658,plain,
    ( spl4_66
    | ~ spl4_1
    | ~ spl4_36
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f1647,f909,f504,f84,f794])).

fof(f794,plain,
    ( spl4_66
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f84,plain,
    ( spl4_1
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f504,plain,
    ( spl4_36
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f909,plain,
    ( spl4_75
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f1647,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_1
    | ~ spl4_36
    | ~ spl4_75 ),
    inference(resolution,[],[f1111,f86])).

fof(f86,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1111,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_36
    | ~ spl4_75 ),
    inference(backward_demodulation,[],[f528,f911])).

fof(f911,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f909])).

fof(f528,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK3))
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_36 ),
    inference(resolution,[],[f505,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f505,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f504])).

fof(f1652,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k7_relat_1(sK3,sK2)
    | k1_xboole_0 != sK2
    | k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1446,plain,
    ( spl4_90
    | ~ spl4_10
    | spl4_110 ),
    inference(avatar_split_clause,[],[f1444,f1344,f130,f1105])).

fof(f1105,plain,
    ( spl4_90
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f130,plain,
    ( spl4_10
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1344,plain,
    ( spl4_110
  <=> v1_funct_2(k1_xboole_0,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f1444,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_10
    | spl4_110 ),
    inference(resolution,[],[f1346,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1346,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK2,k1_xboole_0)
    | spl4_110 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f1347,plain,
    ( ~ spl4_110
    | spl4_70
    | ~ spl4_106 ),
    inference(avatar_split_clause,[],[f1310,f1291,f846,f1344])).

fof(f846,plain,
    ( spl4_70
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f1291,plain,
    ( spl4_106
  <=> k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f1310,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK2,k1_xboole_0)
    | spl4_70
    | ~ spl4_106 ),
    inference(backward_demodulation,[],[f848,f1293])).

fof(f1293,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK2)
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f1291])).

fof(f848,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | spl4_70 ),
    inference(avatar_component_clause,[],[f846])).

fof(f1294,plain,
    ( spl4_106
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f1278,f484,f1291])).

fof(f484,plain,
    ( spl4_32
  <=> r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1278,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK2)
    | ~ spl4_32 ),
    inference(resolution,[],[f485,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f485,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f484])).

fof(f1234,plain,
    ( spl4_102
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f1216,f641,f1231])).

fof(f1231,plain,
    ( spl4_102
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f641,plain,
    ( spl4_52
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f1216,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_52 ),
    inference(resolution,[],[f642,f46])).

fof(f642,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f641])).

fof(f912,plain,
    ( ~ spl4_3
    | spl4_6
    | spl4_75
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f907,f268,f89,f909,f108,f94])).

fof(f94,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f108,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f89,plain,
    ( spl4_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f268,plain,
    ( spl4_24
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f907,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f904,f270])).

fof(f270,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f268])).

fof(f904,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f91])).

fof(f91,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f849,plain,
    ( ~ spl4_70
    | ~ spl4_6
    | spl4_58 ),
    inference(avatar_split_clause,[],[f812,f717,f108,f846])).

fof(f717,plain,
    ( spl4_58
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f812,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)
    | ~ spl4_6
    | spl4_58 ),
    inference(backward_demodulation,[],[f719,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f719,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_58 ),
    inference(avatar_component_clause,[],[f717])).

fof(f844,plain,
    ( ~ spl4_6
    | spl4_32
    | ~ spl4_55 ),
    inference(avatar_contradiction_clause,[],[f843])).

fof(f843,plain,
    ( $false
    | ~ spl4_6
    | spl4_32
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f486,f842])).

fof(f842,plain,
    ( ! [X2] : r1_tarski(k7_relat_1(sK3,X2),k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f811,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f811,plain,
    ( ! [X2] : r1_tarski(k7_relat_1(sK3,X2),k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_55 ),
    inference(backward_demodulation,[],[f693,f109])).

fof(f693,plain,
    ( ! [X2] : r1_tarski(k7_relat_1(sK3,X2),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_55 ),
    inference(resolution,[],[f680,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f680,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f679])).

fof(f679,plain,
    ( spl4_55
  <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f486,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f484])).

fof(f822,plain,
    ( spl4_52
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f821,f159,f108,f641])).

fof(f159,plain,
    ( spl4_15
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f821,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f801,f76])).

fof(f801,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(backward_demodulation,[],[f161,f109])).

fof(f161,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f797,plain,
    ( spl4_58
    | spl4_6
    | ~ spl4_66
    | ~ spl4_47
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f792,f734,f591,f794,f108,f717])).

fof(f591,plain,
    ( spl4_47
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f734,plain,
    ( spl4_59
  <=> k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f792,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_47
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f782,f736])).

fof(f736,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f734])).

fof(f782,plain,
    ( k1_xboole_0 = sK1
    | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_47 ),
    inference(resolution,[],[f69,f592])).

fof(f592,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f591])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f737,plain,
    ( spl4_59
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f729,f591,f734])).

fof(f729,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | ~ spl4_47 ),
    inference(resolution,[],[f592,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f720,plain,
    ( ~ spl4_58
    | ~ spl4_2
    | ~ spl4_4
    | spl4_8 ),
    inference(avatar_split_clause,[],[f715,f117,f99,f89,f717])).

fof(f99,plain,
    ( spl4_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f117,plain,
    ( spl4_8
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f715,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_8 ),
    inference(forward_demodulation,[],[f119,f472])).

fof(f472,plain,
    ( ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f469,f91])).

fof(f469,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_4 ),
    inference(resolution,[],[f71,f101])).

fof(f101,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f119,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f713,plain,
    ( ~ spl4_36
    | spl4_57 ),
    inference(avatar_split_clause,[],[f711,f699,f504])).

fof(f699,plain,
    ( spl4_57
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f711,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_57 ),
    inference(resolution,[],[f701,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f701,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | spl4_57 ),
    inference(avatar_component_clause,[],[f699])).

fof(f704,plain,
    ( ~ spl4_57
    | ~ spl4_2
    | ~ spl4_4
    | spl4_29 ),
    inference(avatar_split_clause,[],[f703,f439,f99,f89,f699])).

fof(f439,plain,
    ( spl4_29
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f703,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_29 ),
    inference(forward_demodulation,[],[f441,f472])).

fof(f441,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f439])).

fof(f702,plain,
    ( ~ spl4_34
    | ~ spl4_48
    | ~ spl4_57
    | spl4_47 ),
    inference(avatar_split_clause,[],[f654,f591,f699,f597,f494])).

fof(f494,plain,
    ( spl4_34
  <=> v1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f597,plain,
    ( spl4_48
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f654,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_47 ),
    inference(resolution,[],[f593,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f593,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_47 ),
    inference(avatar_component_clause,[],[f591])).

fof(f697,plain,
    ( spl4_54
    | ~ spl4_55 ),
    inference(avatar_contradiction_clause,[],[f689])).

fof(f689,plain,
    ( $false
    | spl4_54
    | ~ spl4_55 ),
    inference(unit_resulting_resolution,[],[f673,f680,f57])).

fof(f673,plain,
    ( ! [X1] : ~ r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(X1,sK1))
    | spl4_54 ),
    inference(resolution,[],[f662,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f662,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl4_54 ),
    inference(resolution,[],[f660,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f660,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl4_54 ),
    inference(avatar_component_clause,[],[f658])).

fof(f658,plain,
    ( spl4_54
  <=> v5_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f681,plain,
    ( ~ spl4_4
    | ~ spl4_2
    | spl4_55
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f676,f99,f89,f679,f89,f99])).

fof(f676,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(superposition,[],[f73,f472])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f661,plain,
    ( ~ spl4_54
    | ~ spl4_34
    | spl4_48 ),
    inference(avatar_split_clause,[],[f656,f597,f494,f658])).

fof(f656,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v5_relat_1(k7_relat_1(sK3,sK2),sK1)
    | spl4_48 ),
    inference(resolution,[],[f599,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f599,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | spl4_48 ),
    inference(avatar_component_clause,[],[f597])).

fof(f600,plain,
    ( ~ spl4_48
    | ~ spl4_2
    | ~ spl4_4
    | spl4_28 ),
    inference(avatar_split_clause,[],[f595,f435,f99,f89,f597])).

fof(f435,plain,
    ( spl4_28
  <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f595,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ spl4_2
    | ~ spl4_4
    | spl4_28 ),
    inference(forward_demodulation,[],[f437,f472])).

fof(f437,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f435])).

fof(f580,plain,
    ( ~ spl4_36
    | spl4_34 ),
    inference(avatar_split_clause,[],[f577,f494,f504])).

fof(f577,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_34 ),
    inference(resolution,[],[f496,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f496,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f494])).

fof(f527,plain,
    ( ~ spl4_2
    | spl4_36 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl4_2
    | spl4_36 ),
    inference(subsumption_resolution,[],[f91,f524])).

fof(f524,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_36 ),
    inference(resolution,[],[f506,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f506,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f504])).

fof(f497,plain,
    ( ~ spl4_34
    | ~ spl4_2
    | ~ spl4_4
    | spl4_27 ),
    inference(avatar_split_clause,[],[f481,f431,f99,f89,f494])).

fof(f431,plain,
    ( spl4_27
  <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f481,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_2
    | ~ spl4_4
    | spl4_27 ),
    inference(backward_demodulation,[],[f433,f472])).

fof(f433,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f431])).

fof(f442,plain,
    ( ~ spl4_27
    | ~ spl4_28
    | ~ spl4_29
    | spl4_7 ),
    inference(avatar_split_clause,[],[f427,f113,f439,f435,f431])).

fof(f113,plain,
    ( spl4_7
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f427,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_7 ),
    inference(resolution,[],[f61,f115])).

fof(f115,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f297,plain,
    ( ~ spl4_4
    | ~ spl4_2
    | spl4_9 ),
    inference(avatar_split_clause,[],[f295,f121,f89,f99])).

fof(f121,plain,
    ( spl4_9
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f295,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_9 ),
    inference(resolution,[],[f72,f123])).

fof(f123,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f271,plain,
    ( spl4_24
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f263,f89,f268])).

fof(f263,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f63,f91])).

fof(f162,plain,
    ( spl4_15
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f155,f89,f159])).

fof(f155,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f57,f91])).

fof(f149,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f74,f135,f56])).

fof(f135,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f136,plain,
    ( spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f128,f133,f130])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f82,f76])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f124,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f40,f121,f117,f113])).

fof(f40,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f111,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f41,f108,f104])).

fof(f104,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f41,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f97,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f89])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:17:25 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (2387)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.46  % (2367)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (2373)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (2377)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (2372)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (2389)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (2369)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (2381)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (2375)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (2370)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (2378)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (2371)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (2388)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (2385)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (2376)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (2380)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (2390)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (2384)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (2379)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (2383)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (2368)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (2386)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (2391)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.56  % (2366)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.57  % (2382)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.81/0.60  % (2374)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.81/0.60  % (2381)Refutation found. Thanks to Tanya!
% 1.81/0.60  % SZS status Theorem for theBenchmark
% 1.81/0.60  % SZS output start Proof for theBenchmark
% 1.81/0.60  fof(f1686,plain,(
% 1.81/0.60    $false),
% 1.81/0.60    inference(avatar_sat_refutation,[],[f87,f92,f97,f102,f111,f124,f136,f149,f162,f271,f297,f442,f497,f527,f580,f600,f661,f681,f697,f702,f704,f713,f720,f737,f797,f822,f844,f849,f912,f1234,f1294,f1347,f1446,f1652,f1658])).
% 1.81/0.60  fof(f1658,plain,(
% 1.81/0.60    spl4_66 | ~spl4_1 | ~spl4_36 | ~spl4_75),
% 1.81/0.60    inference(avatar_split_clause,[],[f1647,f909,f504,f84,f794])).
% 1.81/0.60  fof(f794,plain,(
% 1.81/0.60    spl4_66 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.81/0.60  fof(f84,plain,(
% 1.81/0.60    spl4_1 <=> r1_tarski(sK2,sK0)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.81/0.60  fof(f504,plain,(
% 1.81/0.60    spl4_36 <=> v1_relat_1(sK3)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.81/0.60  fof(f909,plain,(
% 1.81/0.60    spl4_75 <=> sK0 = k1_relat_1(sK3)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 1.81/0.60  fof(f1647,plain,(
% 1.81/0.60    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_1 | ~spl4_36 | ~spl4_75)),
% 1.81/0.60    inference(resolution,[],[f1111,f86])).
% 1.81/0.60  fof(f86,plain,(
% 1.81/0.60    r1_tarski(sK2,sK0) | ~spl4_1),
% 1.81/0.60    inference(avatar_component_clause,[],[f84])).
% 1.81/0.60  fof(f1111,plain,(
% 1.81/0.60    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | (~spl4_36 | ~spl4_75)),
% 1.81/0.60    inference(backward_demodulation,[],[f528,f911])).
% 1.81/0.60  fof(f911,plain,(
% 1.81/0.60    sK0 = k1_relat_1(sK3) | ~spl4_75),
% 1.81/0.60    inference(avatar_component_clause,[],[f909])).
% 1.81/0.60  fof(f528,plain,(
% 1.81/0.60    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK3)) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_36),
% 1.81/0.60    inference(resolution,[],[f505,f50])).
% 1.81/0.60  fof(f50,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.81/0.60    inference(cnf_transformation,[],[f27])).
% 1.81/0.60  fof(f27,plain,(
% 1.81/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(flattening,[],[f26])).
% 1.81/0.60  fof(f26,plain,(
% 1.81/0.60    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f9])).
% 1.81/0.60  fof(f9,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.81/0.60  fof(f505,plain,(
% 1.81/0.60    v1_relat_1(sK3) | ~spl4_36),
% 1.81/0.60    inference(avatar_component_clause,[],[f504])).
% 1.81/0.60  fof(f1652,plain,(
% 1.81/0.60    k1_xboole_0 != sK3 | k1_xboole_0 != k7_relat_1(sK3,sK2) | k1_xboole_0 != sK2 | k1_xboole_0 != sK0 | k1_xboole_0 != sK1 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_2(sK3,sK0,sK1)),
% 1.81/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.81/0.60  fof(f1446,plain,(
% 1.81/0.60    spl4_90 | ~spl4_10 | spl4_110),
% 1.81/0.60    inference(avatar_split_clause,[],[f1444,f1344,f130,f1105])).
% 1.81/0.60  fof(f1105,plain,(
% 1.81/0.60    spl4_90 <=> k1_xboole_0 = sK2),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 1.81/0.60  fof(f130,plain,(
% 1.81/0.60    spl4_10 <=> ! [X0] : (k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.81/0.60  fof(f1344,plain,(
% 1.81/0.60    spl4_110 <=> v1_funct_2(k1_xboole_0,sK2,k1_xboole_0)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).
% 1.81/0.60  fof(f1444,plain,(
% 1.81/0.60    k1_xboole_0 = sK2 | (~spl4_10 | spl4_110)),
% 1.81/0.60    inference(resolution,[],[f1346,f131])).
% 1.81/0.60  fof(f131,plain,(
% 1.81/0.60    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_10),
% 1.81/0.60    inference(avatar_component_clause,[],[f130])).
% 1.81/0.60  fof(f1346,plain,(
% 1.81/0.60    ~v1_funct_2(k1_xboole_0,sK2,k1_xboole_0) | spl4_110),
% 1.81/0.60    inference(avatar_component_clause,[],[f1344])).
% 1.81/0.60  fof(f1347,plain,(
% 1.81/0.60    ~spl4_110 | spl4_70 | ~spl4_106),
% 1.81/0.60    inference(avatar_split_clause,[],[f1310,f1291,f846,f1344])).
% 1.81/0.60  fof(f846,plain,(
% 1.81/0.60    spl4_70 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 1.81/0.60  fof(f1291,plain,(
% 1.81/0.60    spl4_106 <=> k1_xboole_0 = k7_relat_1(sK3,sK2)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).
% 1.81/0.60  fof(f1310,plain,(
% 1.81/0.60    ~v1_funct_2(k1_xboole_0,sK2,k1_xboole_0) | (spl4_70 | ~spl4_106)),
% 1.81/0.60    inference(backward_demodulation,[],[f848,f1293])).
% 1.81/0.60  fof(f1293,plain,(
% 1.81/0.60    k1_xboole_0 = k7_relat_1(sK3,sK2) | ~spl4_106),
% 1.81/0.60    inference(avatar_component_clause,[],[f1291])).
% 1.81/0.60  fof(f848,plain,(
% 1.81/0.60    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | spl4_70),
% 1.81/0.60    inference(avatar_component_clause,[],[f846])).
% 1.81/0.60  fof(f1294,plain,(
% 1.81/0.60    spl4_106 | ~spl4_32),
% 1.81/0.60    inference(avatar_split_clause,[],[f1278,f484,f1291])).
% 1.81/0.60  fof(f484,plain,(
% 1.81/0.60    spl4_32 <=> r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.81/0.60  fof(f1278,plain,(
% 1.81/0.60    k1_xboole_0 = k7_relat_1(sK3,sK2) | ~spl4_32),
% 1.81/0.60    inference(resolution,[],[f485,f46])).
% 1.81/0.60  fof(f46,plain,(
% 1.81/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.81/0.60    inference(cnf_transformation,[],[f22])).
% 1.81/0.60  fof(f22,plain,(
% 1.81/0.60    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.81/0.60    inference(ennf_transformation,[],[f2])).
% 1.81/0.60  fof(f2,axiom,(
% 1.81/0.60    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.81/0.60  fof(f485,plain,(
% 1.81/0.60    r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) | ~spl4_32),
% 1.81/0.60    inference(avatar_component_clause,[],[f484])).
% 1.81/0.60  fof(f1234,plain,(
% 1.81/0.60    spl4_102 | ~spl4_52),
% 1.81/0.60    inference(avatar_split_clause,[],[f1216,f641,f1231])).
% 1.81/0.60  fof(f1231,plain,(
% 1.81/0.60    spl4_102 <=> k1_xboole_0 = sK3),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).
% 1.81/0.60  fof(f641,plain,(
% 1.81/0.60    spl4_52 <=> r1_tarski(sK3,k1_xboole_0)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.81/0.60  fof(f1216,plain,(
% 1.81/0.60    k1_xboole_0 = sK3 | ~spl4_52),
% 1.81/0.60    inference(resolution,[],[f642,f46])).
% 1.81/0.60  fof(f642,plain,(
% 1.81/0.60    r1_tarski(sK3,k1_xboole_0) | ~spl4_52),
% 1.81/0.60    inference(avatar_component_clause,[],[f641])).
% 1.81/0.60  fof(f912,plain,(
% 1.81/0.60    ~spl4_3 | spl4_6 | spl4_75 | ~spl4_2 | ~spl4_24),
% 1.81/0.60    inference(avatar_split_clause,[],[f907,f268,f89,f909,f108,f94])).
% 1.81/0.60  fof(f94,plain,(
% 1.81/0.60    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.81/0.60  fof(f108,plain,(
% 1.81/0.60    spl4_6 <=> k1_xboole_0 = sK1),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.81/0.60  fof(f89,plain,(
% 1.81/0.60    spl4_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.81/0.60  fof(f268,plain,(
% 1.81/0.60    spl4_24 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.81/0.60  fof(f907,plain,(
% 1.81/0.60    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | (~spl4_2 | ~spl4_24)),
% 1.81/0.60    inference(forward_demodulation,[],[f904,f270])).
% 1.81/0.60  fof(f270,plain,(
% 1.81/0.60    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_24),
% 1.81/0.60    inference(avatar_component_clause,[],[f268])).
% 1.81/0.60  fof(f904,plain,(
% 1.81/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl4_2),
% 1.81/0.60    inference(resolution,[],[f70,f91])).
% 1.81/0.60  fof(f91,plain,(
% 1.81/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_2),
% 1.81/0.60    inference(avatar_component_clause,[],[f89])).
% 1.81/0.60  fof(f70,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f35])).
% 1.81/0.60  fof(f35,plain,(
% 1.81/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.60    inference(flattening,[],[f34])).
% 1.81/0.60  fof(f34,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.60    inference(ennf_transformation,[],[f14])).
% 1.81/0.60  fof(f14,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.81/0.60  fof(f849,plain,(
% 1.81/0.60    ~spl4_70 | ~spl4_6 | spl4_58),
% 1.81/0.60    inference(avatar_split_clause,[],[f812,f717,f108,f846])).
% 1.81/0.60  fof(f717,plain,(
% 1.81/0.60    spl4_58 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 1.81/0.60  fof(f812,plain,(
% 1.81/0.60    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,k1_xboole_0) | (~spl4_6 | spl4_58)),
% 1.81/0.60    inference(backward_demodulation,[],[f719,f109])).
% 1.81/0.60  fof(f109,plain,(
% 1.81/0.60    k1_xboole_0 = sK1 | ~spl4_6),
% 1.81/0.60    inference(avatar_component_clause,[],[f108])).
% 1.81/0.60  fof(f719,plain,(
% 1.81/0.60    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_58),
% 1.81/0.60    inference(avatar_component_clause,[],[f717])).
% 1.81/0.60  fof(f844,plain,(
% 1.81/0.60    ~spl4_6 | spl4_32 | ~spl4_55),
% 1.81/0.60    inference(avatar_contradiction_clause,[],[f843])).
% 1.81/0.60  fof(f843,plain,(
% 1.81/0.60    $false | (~spl4_6 | spl4_32 | ~spl4_55)),
% 1.81/0.60    inference(subsumption_resolution,[],[f486,f842])).
% 1.81/0.60  fof(f842,plain,(
% 1.81/0.60    ( ! [X2] : (r1_tarski(k7_relat_1(sK3,X2),k1_xboole_0)) ) | (~spl4_6 | ~spl4_55)),
% 1.81/0.60    inference(forward_demodulation,[],[f811,f76])).
% 1.81/0.60  fof(f76,plain,(
% 1.81/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.81/0.60    inference(equality_resolution,[],[f60])).
% 1.81/0.60  fof(f60,plain,(
% 1.81/0.60    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f3])).
% 1.81/0.60  fof(f3,axiom,(
% 1.81/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.81/0.60  fof(f811,plain,(
% 1.81/0.60    ( ! [X2] : (r1_tarski(k7_relat_1(sK3,X2),k2_zfmisc_1(sK0,k1_xboole_0))) ) | (~spl4_6 | ~spl4_55)),
% 1.81/0.60    inference(backward_demodulation,[],[f693,f109])).
% 1.81/0.60  fof(f693,plain,(
% 1.81/0.60    ( ! [X2] : (r1_tarski(k7_relat_1(sK3,X2),k2_zfmisc_1(sK0,sK1))) ) | ~spl4_55),
% 1.81/0.60    inference(resolution,[],[f680,f57])).
% 1.81/0.60  fof(f57,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f4])).
% 1.81/0.60  fof(f4,axiom,(
% 1.81/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.81/0.60  fof(f680,plain,(
% 1.81/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_55),
% 1.81/0.60    inference(avatar_component_clause,[],[f679])).
% 1.81/0.60  fof(f679,plain,(
% 1.81/0.60    spl4_55 <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.81/0.60  fof(f486,plain,(
% 1.81/0.60    ~r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) | spl4_32),
% 1.81/0.60    inference(avatar_component_clause,[],[f484])).
% 1.81/0.60  fof(f822,plain,(
% 1.81/0.60    spl4_52 | ~spl4_6 | ~spl4_15),
% 1.81/0.60    inference(avatar_split_clause,[],[f821,f159,f108,f641])).
% 1.81/0.60  fof(f159,plain,(
% 1.81/0.60    spl4_15 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.81/0.60  fof(f821,plain,(
% 1.81/0.60    r1_tarski(sK3,k1_xboole_0) | (~spl4_6 | ~spl4_15)),
% 1.81/0.60    inference(forward_demodulation,[],[f801,f76])).
% 1.81/0.60  fof(f801,plain,(
% 1.81/0.60    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl4_6 | ~spl4_15)),
% 1.81/0.60    inference(backward_demodulation,[],[f161,f109])).
% 1.81/0.60  fof(f161,plain,(
% 1.81/0.60    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_15),
% 1.81/0.60    inference(avatar_component_clause,[],[f159])).
% 1.81/0.60  fof(f797,plain,(
% 1.81/0.60    spl4_58 | spl4_6 | ~spl4_66 | ~spl4_47 | ~spl4_59),
% 1.81/0.60    inference(avatar_split_clause,[],[f792,f734,f591,f794,f108,f717])).
% 1.81/0.60  fof(f591,plain,(
% 1.81/0.60    spl4_47 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.81/0.60  fof(f734,plain,(
% 1.81/0.60    spl4_59 <=> k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.81/0.60  fof(f792,plain,(
% 1.81/0.60    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_47 | ~spl4_59)),
% 1.81/0.60    inference(forward_demodulation,[],[f782,f736])).
% 1.81/0.60  fof(f736,plain,(
% 1.81/0.60    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_59),
% 1.81/0.60    inference(avatar_component_clause,[],[f734])).
% 1.81/0.60  fof(f782,plain,(
% 1.81/0.60    k1_xboole_0 = sK1 | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~spl4_47),
% 1.81/0.60    inference(resolution,[],[f69,f592])).
% 1.81/0.60  fof(f592,plain,(
% 1.81/0.60    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl4_47),
% 1.81/0.60    inference(avatar_component_clause,[],[f591])).
% 1.81/0.60  fof(f69,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f35])).
% 1.81/0.60  fof(f737,plain,(
% 1.81/0.60    spl4_59 | ~spl4_47),
% 1.81/0.60    inference(avatar_split_clause,[],[f729,f591,f734])).
% 1.81/0.60  fof(f729,plain,(
% 1.81/0.60    k1_relat_1(k7_relat_1(sK3,sK2)) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | ~spl4_47),
% 1.81/0.60    inference(resolution,[],[f592,f63])).
% 1.81/0.60  fof(f63,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f32])).
% 1.81/0.60  fof(f32,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.60    inference(ennf_transformation,[],[f12])).
% 1.81/0.60  fof(f12,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.81/0.60  fof(f720,plain,(
% 1.81/0.60    ~spl4_58 | ~spl4_2 | ~spl4_4 | spl4_8),
% 1.81/0.60    inference(avatar_split_clause,[],[f715,f117,f99,f89,f717])).
% 1.81/0.60  fof(f99,plain,(
% 1.81/0.60    spl4_4 <=> v1_funct_1(sK3)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.81/0.60  fof(f117,plain,(
% 1.81/0.60    spl4_8 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.81/0.60  fof(f715,plain,(
% 1.81/0.60    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_2 | ~spl4_4 | spl4_8)),
% 1.81/0.60    inference(forward_demodulation,[],[f119,f472])).
% 1.81/0.60  fof(f472,plain,(
% 1.81/0.60    ( ! [X0] : (k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)) ) | (~spl4_2 | ~spl4_4)),
% 1.81/0.60    inference(resolution,[],[f469,f91])).
% 1.81/0.60  fof(f469,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_4),
% 1.81/0.60    inference(resolution,[],[f71,f101])).
% 1.81/0.60  fof(f101,plain,(
% 1.81/0.60    v1_funct_1(sK3) | ~spl4_4),
% 1.81/0.60    inference(avatar_component_clause,[],[f99])).
% 1.81/0.60  fof(f71,plain,(
% 1.81/0.60    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f37])).
% 1.81/0.60  fof(f37,plain,(
% 1.81/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.81/0.60    inference(flattening,[],[f36])).
% 1.81/0.60  fof(f36,plain,(
% 1.81/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.81/0.60    inference(ennf_transformation,[],[f16])).
% 1.81/0.60  fof(f16,axiom,(
% 1.81/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.81/0.60  fof(f119,plain,(
% 1.81/0.60    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_8),
% 1.81/0.60    inference(avatar_component_clause,[],[f117])).
% 1.81/0.60  fof(f713,plain,(
% 1.81/0.60    ~spl4_36 | spl4_57),
% 1.81/0.60    inference(avatar_split_clause,[],[f711,f699,f504])).
% 1.81/0.60  fof(f699,plain,(
% 1.81/0.60    spl4_57 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.81/0.60  fof(f711,plain,(
% 1.81/0.60    ~v1_relat_1(sK3) | spl4_57),
% 1.81/0.60    inference(resolution,[],[f701,f49])).
% 1.81/0.60  fof(f49,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f25])).
% 1.81/0.60  fof(f25,plain,(
% 1.81/0.60    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f7])).
% 1.81/0.60  fof(f7,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.81/0.60  fof(f701,plain,(
% 1.81/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | spl4_57),
% 1.81/0.60    inference(avatar_component_clause,[],[f699])).
% 1.81/0.60  fof(f704,plain,(
% 1.81/0.60    ~spl4_57 | ~spl4_2 | ~spl4_4 | spl4_29),
% 1.81/0.60    inference(avatar_split_clause,[],[f703,f439,f99,f89,f699])).
% 1.81/0.60  fof(f439,plain,(
% 1.81/0.60    spl4_29 <=> r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.81/0.60  fof(f703,plain,(
% 1.81/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | (~spl4_2 | ~spl4_4 | spl4_29)),
% 1.81/0.60    inference(forward_demodulation,[],[f441,f472])).
% 1.81/0.60  fof(f441,plain,(
% 1.81/0.60    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | spl4_29),
% 1.81/0.60    inference(avatar_component_clause,[],[f439])).
% 1.81/0.60  fof(f702,plain,(
% 1.81/0.60    ~spl4_34 | ~spl4_48 | ~spl4_57 | spl4_47),
% 1.81/0.60    inference(avatar_split_clause,[],[f654,f591,f699,f597,f494])).
% 1.81/0.60  fof(f494,plain,(
% 1.81/0.60    spl4_34 <=> v1_relat_1(k7_relat_1(sK3,sK2))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.81/0.60  fof(f597,plain,(
% 1.81/0.60    spl4_48 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 1.81/0.60  fof(f654,plain,(
% 1.81/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_47),
% 1.81/0.60    inference(resolution,[],[f593,f61])).
% 1.81/0.60  fof(f61,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f30])).
% 1.81/0.60  fof(f30,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.81/0.60    inference(flattening,[],[f29])).
% 1.81/0.60  fof(f29,plain,(
% 1.81/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.81/0.60    inference(ennf_transformation,[],[f13])).
% 1.81/0.60  fof(f13,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.81/0.60  fof(f593,plain,(
% 1.81/0.60    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_47),
% 1.81/0.60    inference(avatar_component_clause,[],[f591])).
% 1.81/0.60  fof(f697,plain,(
% 1.81/0.60    spl4_54 | ~spl4_55),
% 1.81/0.60    inference(avatar_contradiction_clause,[],[f689])).
% 1.81/0.60  fof(f689,plain,(
% 1.81/0.60    $false | (spl4_54 | ~spl4_55)),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f673,f680,f57])).
% 1.81/0.60  fof(f673,plain,(
% 1.81/0.60    ( ! [X1] : (~r1_tarski(k7_relat_1(sK3,sK2),k2_zfmisc_1(X1,sK1))) ) | spl4_54),
% 1.81/0.60    inference(resolution,[],[f662,f56])).
% 1.81/0.60  fof(f56,plain,(
% 1.81/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f4])).
% 1.81/0.60  fof(f662,plain,(
% 1.81/0.60    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_54),
% 1.81/0.60    inference(resolution,[],[f660,f64])).
% 1.81/0.60  fof(f64,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f33])).
% 1.81/0.60  fof(f33,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.60    inference(ennf_transformation,[],[f19])).
% 1.81/0.60  fof(f19,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.81/0.60    inference(pure_predicate_removal,[],[f11])).
% 1.81/0.60  fof(f11,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.81/0.60  fof(f660,plain,(
% 1.81/0.60    ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | spl4_54),
% 1.81/0.60    inference(avatar_component_clause,[],[f658])).
% 1.81/0.60  fof(f658,plain,(
% 1.81/0.60    spl4_54 <=> v5_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.81/0.60  fof(f681,plain,(
% 1.81/0.60    ~spl4_4 | ~spl4_2 | spl4_55 | ~spl4_2 | ~spl4_4),
% 1.81/0.60    inference(avatar_split_clause,[],[f676,f99,f89,f679,f89,f99])).
% 1.81/0.60  fof(f676,plain,(
% 1.81/0.60    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) ) | (~spl4_2 | ~spl4_4)),
% 1.81/0.60    inference(superposition,[],[f73,f472])).
% 1.81/0.60  fof(f73,plain,(
% 1.81/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f39])).
% 1.81/0.60  fof(f39,plain,(
% 1.81/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.81/0.60    inference(flattening,[],[f38])).
% 1.81/0.60  fof(f38,plain,(
% 1.81/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.81/0.60    inference(ennf_transformation,[],[f15])).
% 1.81/0.60  fof(f15,axiom,(
% 1.81/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.81/0.60  fof(f661,plain,(
% 1.81/0.60    ~spl4_54 | ~spl4_34 | spl4_48),
% 1.81/0.60    inference(avatar_split_clause,[],[f656,f597,f494,f658])).
% 1.81/0.60  fof(f656,plain,(
% 1.81/0.60    ~v1_relat_1(k7_relat_1(sK3,sK2)) | ~v5_relat_1(k7_relat_1(sK3,sK2),sK1) | spl4_48),
% 1.81/0.60    inference(resolution,[],[f599,f52])).
% 1.81/0.60  fof(f52,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f28])).
% 1.81/0.60  fof(f28,plain,(
% 1.81/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f5])).
% 1.81/0.60  fof(f5,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.81/0.60  fof(f599,plain,(
% 1.81/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | spl4_48),
% 1.81/0.60    inference(avatar_component_clause,[],[f597])).
% 1.81/0.60  fof(f600,plain,(
% 1.81/0.60    ~spl4_48 | ~spl4_2 | ~spl4_4 | spl4_28),
% 1.81/0.60    inference(avatar_split_clause,[],[f595,f435,f99,f89,f597])).
% 1.81/0.60  fof(f435,plain,(
% 1.81/0.60    spl4_28 <=> r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.81/0.60  fof(f595,plain,(
% 1.81/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) | (~spl4_2 | ~spl4_4 | spl4_28)),
% 1.81/0.60    inference(forward_demodulation,[],[f437,f472])).
% 1.81/0.60  fof(f437,plain,(
% 1.81/0.60    ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | spl4_28),
% 1.81/0.60    inference(avatar_component_clause,[],[f435])).
% 1.81/0.60  fof(f580,plain,(
% 1.81/0.60    ~spl4_36 | spl4_34),
% 1.81/0.60    inference(avatar_split_clause,[],[f577,f494,f504])).
% 1.81/0.60  fof(f577,plain,(
% 1.81/0.60    ~v1_relat_1(sK3) | spl4_34),
% 1.81/0.60    inference(resolution,[],[f496,f47])).
% 1.81/0.60  fof(f47,plain,(
% 1.81/0.60    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f23])).
% 1.81/0.60  fof(f23,plain,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.81/0.60    inference(ennf_transformation,[],[f6])).
% 1.81/0.60  fof(f6,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.81/0.61  fof(f496,plain,(
% 1.81/0.61    ~v1_relat_1(k7_relat_1(sK3,sK2)) | spl4_34),
% 1.81/0.61    inference(avatar_component_clause,[],[f494])).
% 1.81/0.61  fof(f527,plain,(
% 1.81/0.61    ~spl4_2 | spl4_36),
% 1.81/0.61    inference(avatar_contradiction_clause,[],[f526])).
% 1.81/0.61  fof(f526,plain,(
% 1.81/0.61    $false | (~spl4_2 | spl4_36)),
% 1.81/0.61    inference(subsumption_resolution,[],[f91,f524])).
% 1.81/0.61  fof(f524,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_36),
% 1.81/0.61    inference(resolution,[],[f506,f62])).
% 1.81/0.61  fof(f62,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f31])).
% 1.81/0.61  fof(f31,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.61    inference(ennf_transformation,[],[f10])).
% 1.81/0.61  fof(f10,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.81/0.61  fof(f506,plain,(
% 1.81/0.61    ~v1_relat_1(sK3) | spl4_36),
% 1.81/0.61    inference(avatar_component_clause,[],[f504])).
% 1.81/0.61  fof(f497,plain,(
% 1.81/0.61    ~spl4_34 | ~spl4_2 | ~spl4_4 | spl4_27),
% 1.81/0.61    inference(avatar_split_clause,[],[f481,f431,f99,f89,f494])).
% 1.81/0.61  fof(f431,plain,(
% 1.81/0.61    spl4_27 <=> v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.81/0.61  fof(f481,plain,(
% 1.81/0.61    ~v1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_2 | ~spl4_4 | spl4_27)),
% 1.81/0.61    inference(backward_demodulation,[],[f433,f472])).
% 1.81/0.61  fof(f433,plain,(
% 1.81/0.61    ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_27),
% 1.81/0.61    inference(avatar_component_clause,[],[f431])).
% 1.81/0.61  fof(f442,plain,(
% 1.81/0.61    ~spl4_27 | ~spl4_28 | ~spl4_29 | spl4_7),
% 1.81/0.61    inference(avatar_split_clause,[],[f427,f113,f439,f435,f431])).
% 1.81/0.61  fof(f113,plain,(
% 1.81/0.61    spl4_7 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.81/0.61  fof(f427,plain,(
% 1.81/0.61    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK2) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_7),
% 1.81/0.61    inference(resolution,[],[f61,f115])).
% 1.81/0.61  fof(f115,plain,(
% 1.81/0.61    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_7),
% 1.81/0.61    inference(avatar_component_clause,[],[f113])).
% 1.81/0.61  fof(f297,plain,(
% 1.81/0.61    ~spl4_4 | ~spl4_2 | spl4_9),
% 1.81/0.61    inference(avatar_split_clause,[],[f295,f121,f89,f99])).
% 1.81/0.61  fof(f121,plain,(
% 1.81/0.61    spl4_9 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.81/0.61  fof(f295,plain,(
% 1.81/0.61    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_9),
% 1.81/0.61    inference(resolution,[],[f72,f123])).
% 1.81/0.61  fof(f123,plain,(
% 1.81/0.61    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_9),
% 1.81/0.61    inference(avatar_component_clause,[],[f121])).
% 1.81/0.61  fof(f72,plain,(
% 1.81/0.61    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f39])).
% 1.81/0.61  fof(f271,plain,(
% 1.81/0.61    spl4_24 | ~spl4_2),
% 1.81/0.61    inference(avatar_split_clause,[],[f263,f89,f268])).
% 1.81/0.61  fof(f263,plain,(
% 1.81/0.61    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_2),
% 1.81/0.61    inference(resolution,[],[f63,f91])).
% 1.81/0.61  fof(f162,plain,(
% 1.81/0.61    spl4_15 | ~spl4_2),
% 1.81/0.61    inference(avatar_split_clause,[],[f155,f89,f159])).
% 1.81/0.61  fof(f155,plain,(
% 1.81/0.61    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_2),
% 1.81/0.61    inference(resolution,[],[f57,f91])).
% 1.81/0.61  fof(f149,plain,(
% 1.81/0.61    spl4_11),
% 1.81/0.61    inference(avatar_contradiction_clause,[],[f147])).
% 1.81/0.61  fof(f147,plain,(
% 1.81/0.61    $false | spl4_11),
% 1.81/0.61    inference(unit_resulting_resolution,[],[f74,f135,f56])).
% 1.81/0.61  fof(f135,plain,(
% 1.81/0.61    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_11),
% 1.81/0.61    inference(avatar_component_clause,[],[f133])).
% 1.81/0.61  fof(f133,plain,(
% 1.81/0.61    spl4_11 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.81/0.61  fof(f74,plain,(
% 1.81/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.81/0.61    inference(equality_resolution,[],[f54])).
% 1.81/0.61  fof(f54,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.81/0.61    inference(cnf_transformation,[],[f1])).
% 1.81/0.61  fof(f1,axiom,(
% 1.81/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.61  fof(f136,plain,(
% 1.81/0.61    spl4_10 | ~spl4_11),
% 1.81/0.61    inference(avatar_split_clause,[],[f128,f133,f130])).
% 1.81/0.61  fof(f128,plain,(
% 1.81/0.61    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.81/0.61    inference(forward_demodulation,[],[f82,f76])).
% 1.81/0.61  fof(f82,plain,(
% 1.81/0.61    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.81/0.61    inference(equality_resolution,[],[f81])).
% 1.81/0.61  fof(f81,plain,(
% 1.81/0.61    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.81/0.61    inference(equality_resolution,[],[f65])).
% 1.81/0.61  fof(f65,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f35])).
% 1.81/0.61  fof(f124,plain,(
% 1.81/0.61    ~spl4_7 | ~spl4_8 | ~spl4_9),
% 1.81/0.61    inference(avatar_split_clause,[],[f40,f121,f117,f113])).
% 1.81/0.61  fof(f40,plain,(
% 1.81/0.61    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.81/0.61    inference(cnf_transformation,[],[f21])).
% 1.81/0.61  fof(f21,plain,(
% 1.81/0.61    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.81/0.61    inference(flattening,[],[f20])).
% 1.81/0.61  fof(f20,plain,(
% 1.81/0.61    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.81/0.61    inference(ennf_transformation,[],[f18])).
% 1.81/0.61  fof(f18,negated_conjecture,(
% 1.81/0.61    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.81/0.61    inference(negated_conjecture,[],[f17])).
% 1.81/0.61  fof(f17,conjecture,(
% 1.81/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.81/0.61  fof(f111,plain,(
% 1.81/0.61    spl4_5 | ~spl4_6),
% 1.81/0.61    inference(avatar_split_clause,[],[f41,f108,f104])).
% 1.81/0.61  fof(f104,plain,(
% 1.81/0.61    spl4_5 <=> k1_xboole_0 = sK0),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.81/0.61  fof(f41,plain,(
% 1.81/0.61    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.81/0.61    inference(cnf_transformation,[],[f21])).
% 1.81/0.61  fof(f102,plain,(
% 1.81/0.61    spl4_4),
% 1.81/0.61    inference(avatar_split_clause,[],[f42,f99])).
% 1.81/0.61  fof(f42,plain,(
% 1.81/0.61    v1_funct_1(sK3)),
% 1.81/0.61    inference(cnf_transformation,[],[f21])).
% 1.81/0.61  fof(f97,plain,(
% 1.81/0.61    spl4_3),
% 1.81/0.61    inference(avatar_split_clause,[],[f43,f94])).
% 1.81/0.61  fof(f43,plain,(
% 1.81/0.61    v1_funct_2(sK3,sK0,sK1)),
% 1.81/0.61    inference(cnf_transformation,[],[f21])).
% 1.81/0.61  fof(f92,plain,(
% 1.81/0.61    spl4_2),
% 1.81/0.61    inference(avatar_split_clause,[],[f44,f89])).
% 1.81/0.61  fof(f44,plain,(
% 1.81/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.81/0.61    inference(cnf_transformation,[],[f21])).
% 1.81/0.61  fof(f87,plain,(
% 1.81/0.61    spl4_1),
% 1.81/0.61    inference(avatar_split_clause,[],[f45,f84])).
% 1.81/0.61  fof(f45,plain,(
% 1.81/0.61    r1_tarski(sK2,sK0)),
% 1.81/0.61    inference(cnf_transformation,[],[f21])).
% 1.81/0.61  % SZS output end Proof for theBenchmark
% 1.81/0.61  % (2381)------------------------------
% 1.81/0.61  % (2381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.61  % (2381)Termination reason: Refutation
% 1.81/0.61  
% 1.81/0.61  % (2381)Memory used [KB]: 7164
% 1.81/0.61  % (2381)Time elapsed: 0.144 s
% 1.81/0.61  % (2381)------------------------------
% 1.81/0.61  % (2381)------------------------------
% 1.81/0.61  % (2365)Success in time 0.25 s
%------------------------------------------------------------------------------
