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
% DateTime   : Thu Dec  3 13:02:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 441 expanded)
%              Number of leaves         :   44 ( 178 expanded)
%              Depth                    :   12
%              Number of atoms          :  693 (1395 expanded)
%              Number of equality atoms :  137 ( 337 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f760,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f98,f104,f109,f122,f131,f138,f142,f152,f169,f174,f183,f209,f223,f266,f274,f279,f286,f333,f340,f379,f412,f433,f500,f545,f601,f632,f641,f655,f727,f756,f757,f759])).

fof(f759,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK0
    | k1_xboole_0 != sK2
    | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f757,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK1
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f756,plain,
    ( spl3_65
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f606,f598,f753])).

fof(f753,plain,
    ( spl3_65
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f598,plain,
    ( spl3_56
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f606,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f602,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f602,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_56 ),
    inference(resolution,[],[f600,f72])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f600,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f598])).

fof(f727,plain,
    ( spl3_59
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_20
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f671,f372,f206,f180,f166,f159,f115,f627])).

fof(f627,plain,
    ( spl3_59
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f115,plain,
    ( spl3_6
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f159,plain,
    ( spl3_13
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f166,plain,
    ( spl3_14
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f180,plain,
    ( spl3_15
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f206,plain,
    ( spl3_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f372,plain,
    ( spl3_32
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f671,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_20
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f670,f71])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f670,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0))))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_20
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f669,f208])).

fof(f208,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f206])).

fof(f669,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f342,f374])).

fof(f374,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f372])).

fof(f342,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f336,f168])).

fof(f168,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f166])).

fof(f336,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f335,f182])).

fof(f182,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f180])).

fof(f335,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f145,f160])).

fof(f160,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f145,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_6 ),
    inference(resolution,[],[f117,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f117,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f655,plain,
    ( ~ spl3_59
    | spl3_31
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f649,f372,f357,f627])).

fof(f357,plain,
    ( spl3_31
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f649,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl3_31
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f358,f374])).

fof(f358,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f357])).

fof(f641,plain,
    ( spl3_8
    | ~ spl3_20
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f640])).

fof(f640,plain,
    ( $false
    | spl3_8
    | ~ spl3_20
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f639,f359])).

fof(f359,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f357])).

fof(f639,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_8
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f638,f71])).

fof(f638,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_8
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f126,f208])).

fof(f126,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f632,plain,
    ( ~ spl3_40
    | spl3_49
    | ~ spl3_59 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | ~ spl3_40
    | spl3_49
    | ~ spl3_59 ),
    inference(subsumption_resolution,[],[f555,f629])).

fof(f629,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f627])).

fof(f555,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_40
    | spl3_49 ),
    inference(forward_demodulation,[],[f554,f71])).

fof(f554,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_40
    | spl3_49 ),
    inference(subsumption_resolution,[],[f553,f441])).

fof(f441,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl3_40
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f553,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_49 ),
    inference(superposition,[],[f544,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f544,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl3_49
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f601,plain,
    ( spl3_56
    | ~ spl3_32
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f532,f426,f372,f598])).

fof(f426,plain,
    ( spl3_38
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f532,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_32
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f428,f374])).

fof(f428,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f426])).

fof(f545,plain,
    ( ~ spl3_49
    | spl3_28
    | ~ spl3_31
    | ~ spl3_32
    | spl3_36 ),
    inference(avatar_split_clause,[],[f540,f409,f372,f357,f276,f542])).

fof(f276,plain,
    ( spl3_28
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f409,plain,
    ( spl3_36
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f540,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl3_28
    | ~ spl3_31
    | ~ spl3_32
    | spl3_36 ),
    inference(forward_demodulation,[],[f539,f374])).

fof(f539,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl3_28
    | ~ spl3_31
    | spl3_36 ),
    inference(subsumption_resolution,[],[f538,f411])).

fof(f411,plain,
    ( k1_xboole_0 != sK0
    | spl3_36 ),
    inference(avatar_component_clause,[],[f409])).

fof(f538,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl3_28
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f281,f359])).

fof(f281,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl3_28 ),
    inference(forward_demodulation,[],[f280,f71])).

fof(f280,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_28 ),
    inference(resolution,[],[f278,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f278,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f276])).

fof(f500,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f433,plain,
    ( ~ spl3_26
    | ~ spl3_27
    | spl3_32
    | spl3_36 ),
    inference(avatar_contradiction_clause,[],[f432])).

fof(f432,plain,
    ( $false
    | ~ spl3_26
    | ~ spl3_27
    | spl3_32
    | spl3_36 ),
    inference(subsumption_resolution,[],[f431,f373])).

fof(f373,plain,
    ( k1_xboole_0 != sK2
    | spl3_32 ),
    inference(avatar_component_clause,[],[f372])).

fof(f431,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_26
    | ~ spl3_27
    | spl3_36 ),
    inference(subsumption_resolution,[],[f430,f411])).

fof(f430,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_26
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f269,f273])).

fof(f273,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl3_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f269,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f267,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f267,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_26 ),
    inference(resolution,[],[f265,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f265,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl3_26
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f412,plain,
    ( ~ spl3_36
    | spl3_21
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f398,f376,f220,f409])).

fof(f220,plain,
    ( spl3_21
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f376,plain,
    ( spl3_33
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f398,plain,
    ( k1_xboole_0 != sK0
    | spl3_21
    | ~ spl3_33 ),
    inference(superposition,[],[f221,f378])).

fof(f378,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f376])).

fof(f221,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f220])).

fof(f379,plain,
    ( spl3_32
    | spl3_33
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f366,f283,f271,f376,f372])).

fof(f283,plain,
    ( spl3_29
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f366,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f365,f273])).

fof(f365,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f363,f70])).

fof(f363,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_29 ),
    inference(resolution,[],[f285,f74])).

fof(f285,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f283])).

fof(f340,plain,
    ( ~ spl3_6
    | spl3_8
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl3_6
    | spl3_8
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f338,f126])).

fof(f338,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f337,f168])).

fof(f337,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f336,f222])).

fof(f222,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f220])).

fof(f333,plain,
    ( ~ spl3_6
    | spl3_9
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | ~ spl3_6
    | spl3_9
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f331,f130])).

fof(f130,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f331,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f330,f168])).

fof(f330,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f329,f222])).

fof(f329,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f328,f182])).

fof(f328,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f144,f160])).

fof(f144,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_6 ),
    inference(resolution,[],[f117,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f286,plain,
    ( spl3_29
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f241,f206,f149,f283])).

fof(f149,plain,
    ( spl3_11
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f241,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(superposition,[],[f151,f208])).

fof(f151,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f279,plain,
    ( ~ spl3_28
    | spl3_9
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f240,f206,f128,f276])).

fof(f240,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_9
    | ~ spl3_20 ),
    inference(superposition,[],[f130,f208])).

fof(f274,plain,
    ( spl3_27
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f243,f206,f101,f271])).

fof(f101,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f243,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f237,f70])).

fof(f237,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(superposition,[],[f103,f208])).

fof(f103,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f266,plain,
    ( spl3_26
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f236,f206,f95,f263])).

fof(f95,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f236,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(superposition,[],[f97,f208])).

fof(f97,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f223,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f212,f202,f101,f220])).

fof(f202,plain,
    ( spl3_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f212,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f210,f103])).

fof(f210,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_19 ),
    inference(superposition,[],[f204,f61])).

fof(f204,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f202])).

fof(f209,plain,
    ( spl3_19
    | spl3_20
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f191,f101,f95,f206,f202])).

fof(f191,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f99,f103])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(resolution,[],[f97,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f183,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f175,f119,f83,f78,f180])).

fof(f78,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f83,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f119,plain,
    ( spl3_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f175,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f93,f120])).

fof(f120,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f93,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f91,f80])).

fof(f80,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f91,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f85,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f85,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f174,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7
    | spl3_13 ),
    inference(subsumption_resolution,[],[f172,f120])).

fof(f172,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_13 ),
    inference(subsumption_resolution,[],[f170,f80])).

fof(f170,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(resolution,[],[f161,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f161,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f169,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f164,f135,f119,f83,f78,f166])).

fof(f135,plain,
    ( spl3_10
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f164,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f163,f137])).

fof(f137,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f163,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f92,f120])).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f90,f80])).

fof(f90,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f85,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f152,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f147,f135,f119,f78,f149])).

fof(f147,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f146,f137])).

fof(f146,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f88,f120])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f80,f49])).

fof(f142,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl3_4
    | spl3_7 ),
    inference(resolution,[],[f132,f103])).

fof(f132,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_7 ),
    inference(resolution,[],[f121,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f121,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f138,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f112,f106,f101,f135])).

fof(f106,plain,
    ( spl3_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f110,f103])).

fof(f110,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_5 ),
    inference(superposition,[],[f108,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f108,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f131,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f37,f115,f128,f124])).

fof(f37,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f122,plain,
    ( spl3_6
    | ~ spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f87,f78,f119,f115])).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f109,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f42,f106])).

fof(f42,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f101])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f39,f95])).

fof(f39,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f41,f83])).

fof(f41,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (9070)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (9065)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (9057)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (9057)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f760,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f81,f86,f98,f104,f109,f122,f131,f138,f142,f152,f169,f174,f183,f209,f223,f266,f274,f279,f286,f333,f340,f379,f412,f433,f500,f545,f601,f632,f641,f655,f727,f756,f757,f759])).
% 0.22/0.52  fof(f759,plain,(
% 0.22/0.52    k1_xboole_0 != sK1 | k1_xboole_0 != sK0 | k1_xboole_0 != sK2 | v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f757,plain,(
% 0.22/0.52    k1_xboole_0 != sK2 | k1_xboole_0 != sK1 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f756,plain,(
% 0.22/0.52    spl3_65 | ~spl3_56),
% 0.22/0.52    inference(avatar_split_clause,[],[f606,f598,f753])).
% 0.22/0.52  fof(f753,plain,(
% 0.22/0.52    spl3_65 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 0.22/0.52  fof(f598,plain,(
% 0.22/0.52    spl3_56 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.22/0.52  fof(f606,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl3_56),
% 0.22/0.52    inference(subsumption_resolution,[],[f602,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.52  fof(f602,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_56),
% 0.22/0.52    inference(resolution,[],[f600,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.52    inference(equality_resolution,[],[f66])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f600,plain,(
% 0.22/0.52    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl3_56),
% 0.22/0.52    inference(avatar_component_clause,[],[f598])).
% 0.22/0.52  fof(f727,plain,(
% 0.22/0.52    spl3_59 | ~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_20 | ~spl3_32),
% 0.22/0.52    inference(avatar_split_clause,[],[f671,f372,f206,f180,f166,f159,f115,f627])).
% 0.22/0.52  fof(f627,plain,(
% 0.22/0.52    spl3_59 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    spl3_6 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl3_13 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    spl3_14 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    spl3_15 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    spl3_20 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.52  fof(f372,plain,(
% 0.22/0.52    spl3_32 <=> k1_xboole_0 = sK2),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.52  fof(f671,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_20 | ~spl3_32)),
% 0.22/0.52    inference(forward_demodulation,[],[f670,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f670,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_20 | ~spl3_32)),
% 0.22/0.52    inference(forward_demodulation,[],[f669,f208])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl3_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f206])).
% 0.22/0.52  fof(f669,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)))) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_32)),
% 0.22/0.52    inference(forward_demodulation,[],[f342,f374])).
% 0.22/0.52  fof(f374,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | ~spl3_32),
% 0.22/0.52    inference(avatar_component_clause,[],[f372])).
% 0.22/0.52  fof(f342,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15)),
% 0.22/0.52    inference(forward_demodulation,[],[f336,f168])).
% 0.22/0.52  fof(f168,plain,(
% 0.22/0.52    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f166])).
% 0.22/0.52  fof(f336,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl3_6 | ~spl3_13 | ~spl3_15)),
% 0.22/0.52    inference(forward_demodulation,[],[f335,f182])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f180])).
% 0.22/0.52  fof(f335,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl3_6 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f145,f160])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    v1_relat_1(k2_funct_1(sK2)) | ~spl3_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f159])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_6),
% 0.22/0.52    inference(resolution,[],[f117,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    v1_funct_1(k2_funct_1(sK2)) | ~spl3_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f115])).
% 0.22/0.52  fof(f655,plain,(
% 0.22/0.52    ~spl3_59 | spl3_31 | ~spl3_32),
% 0.22/0.52    inference(avatar_split_clause,[],[f649,f372,f357,f627])).
% 0.22/0.52  fof(f357,plain,(
% 0.22/0.52    spl3_31 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.52  fof(f649,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl3_31 | ~spl3_32)),
% 0.22/0.52    inference(forward_demodulation,[],[f358,f374])).
% 0.22/0.52  fof(f358,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | spl3_31),
% 0.22/0.52    inference(avatar_component_clause,[],[f357])).
% 0.22/0.52  fof(f641,plain,(
% 0.22/0.52    spl3_8 | ~spl3_20 | ~spl3_31),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f640])).
% 0.22/0.52  fof(f640,plain,(
% 0.22/0.52    $false | (spl3_8 | ~spl3_20 | ~spl3_31)),
% 0.22/0.52    inference(subsumption_resolution,[],[f639,f359])).
% 0.22/0.52  fof(f359,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl3_31),
% 0.22/0.52    inference(avatar_component_clause,[],[f357])).
% 0.22/0.52  fof(f639,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl3_8 | ~spl3_20)),
% 0.22/0.52    inference(forward_demodulation,[],[f638,f71])).
% 0.22/0.52  fof(f638,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_8 | ~spl3_20)),
% 0.22/0.52    inference(forward_demodulation,[],[f126,f208])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f124])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    spl3_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.52  fof(f632,plain,(
% 0.22/0.52    ~spl3_40 | spl3_49 | ~spl3_59),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f631])).
% 0.22/0.52  fof(f631,plain,(
% 0.22/0.52    $false | (~spl3_40 | spl3_49 | ~spl3_59)),
% 0.22/0.52    inference(subsumption_resolution,[],[f555,f629])).
% 0.22/0.52  fof(f629,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_59),
% 0.22/0.52    inference(avatar_component_clause,[],[f627])).
% 0.22/0.52  fof(f555,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_40 | spl3_49)),
% 0.22/0.52    inference(forward_demodulation,[],[f554,f71])).
% 0.22/0.52  fof(f554,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_40 | spl3_49)),
% 0.22/0.52    inference(subsumption_resolution,[],[f553,f441])).
% 0.22/0.52  fof(f441,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_40),
% 0.22/0.52    inference(avatar_component_clause,[],[f439])).
% 0.22/0.52  fof(f439,plain,(
% 0.22/0.52    spl3_40 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.52  fof(f553,plain,(
% 0.22/0.52    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_49),
% 0.22/0.52    inference(superposition,[],[f544,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f544,plain,(
% 0.22/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | spl3_49),
% 0.22/0.52    inference(avatar_component_clause,[],[f542])).
% 0.22/0.52  fof(f542,plain,(
% 0.22/0.52    spl3_49 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.52  fof(f601,plain,(
% 0.22/0.52    spl3_56 | ~spl3_32 | ~spl3_38),
% 0.22/0.52    inference(avatar_split_clause,[],[f532,f426,f372,f598])).
% 0.22/0.52  fof(f426,plain,(
% 0.22/0.52    spl3_38 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.52  fof(f532,plain,(
% 0.22/0.52    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_32 | ~spl3_38)),
% 0.22/0.52    inference(forward_demodulation,[],[f428,f374])).
% 0.22/0.52  fof(f428,plain,(
% 0.22/0.52    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl3_38),
% 0.22/0.52    inference(avatar_component_clause,[],[f426])).
% 0.22/0.52  fof(f545,plain,(
% 0.22/0.52    ~spl3_49 | spl3_28 | ~spl3_31 | ~spl3_32 | spl3_36),
% 0.22/0.52    inference(avatar_split_clause,[],[f540,f409,f372,f357,f276,f542])).
% 0.22/0.52  fof(f276,plain,(
% 0.22/0.52    spl3_28 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.52  fof(f409,plain,(
% 0.22/0.52    spl3_36 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.52  fof(f540,plain,(
% 0.22/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (spl3_28 | ~spl3_31 | ~spl3_32 | spl3_36)),
% 0.22/0.52    inference(forward_demodulation,[],[f539,f374])).
% 0.22/0.52  fof(f539,plain,(
% 0.22/0.52    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl3_28 | ~spl3_31 | spl3_36)),
% 0.22/0.52    inference(subsumption_resolution,[],[f538,f411])).
% 0.22/0.52  fof(f411,plain,(
% 0.22/0.52    k1_xboole_0 != sK0 | spl3_36),
% 0.22/0.52    inference(avatar_component_clause,[],[f409])).
% 0.22/0.52  fof(f538,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl3_28 | ~spl3_31)),
% 0.22/0.52    inference(subsumption_resolution,[],[f281,f359])).
% 0.22/0.52  fof(f281,plain,(
% 0.22/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | spl3_28),
% 0.22/0.52    inference(forward_demodulation,[],[f280,f71])).
% 0.22/0.52  fof(f280,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_28),
% 0.22/0.52    inference(resolution,[],[f278,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f278,plain,(
% 0.22/0.52    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | spl3_28),
% 0.22/0.52    inference(avatar_component_clause,[],[f276])).
% 0.22/0.52  fof(f500,plain,(
% 0.22/0.52    k1_xboole_0 != sK2 | sK1 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f433,plain,(
% 0.22/0.52    ~spl3_26 | ~spl3_27 | spl3_32 | spl3_36),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f432])).
% 0.22/0.52  fof(f432,plain,(
% 0.22/0.52    $false | (~spl3_26 | ~spl3_27 | spl3_32 | spl3_36)),
% 0.22/0.52    inference(subsumption_resolution,[],[f431,f373])).
% 0.22/0.52  fof(f373,plain,(
% 0.22/0.52    k1_xboole_0 != sK2 | spl3_32),
% 0.22/0.52    inference(avatar_component_clause,[],[f372])).
% 0.22/0.52  fof(f431,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | (~spl3_26 | ~spl3_27 | spl3_36)),
% 0.22/0.52    inference(subsumption_resolution,[],[f430,f411])).
% 0.22/0.52  fof(f430,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl3_26 | ~spl3_27)),
% 0.22/0.52    inference(subsumption_resolution,[],[f269,f273])).
% 0.22/0.52  fof(f273,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_27),
% 0.22/0.52    inference(avatar_component_clause,[],[f271])).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    spl3_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl3_26),
% 0.22/0.52    inference(forward_demodulation,[],[f267,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f58])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f267,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_26),
% 0.22/0.52    inference(resolution,[],[f265,f74])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.22/0.52    inference(equality_resolution,[],[f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl3_26),
% 0.22/0.52    inference(avatar_component_clause,[],[f263])).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    spl3_26 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.52  fof(f412,plain,(
% 0.22/0.52    ~spl3_36 | spl3_21 | ~spl3_33),
% 0.22/0.52    inference(avatar_split_clause,[],[f398,f376,f220,f409])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    spl3_21 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.52  fof(f376,plain,(
% 0.22/0.52    spl3_33 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.52  fof(f398,plain,(
% 0.22/0.52    k1_xboole_0 != sK0 | (spl3_21 | ~spl3_33)),
% 0.22/0.52    inference(superposition,[],[f221,f378])).
% 0.22/0.52  fof(f378,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_33),
% 0.22/0.52    inference(avatar_component_clause,[],[f376])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    sK0 != k1_relat_1(sK2) | spl3_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f220])).
% 0.22/0.52  fof(f379,plain,(
% 0.22/0.52    spl3_32 | spl3_33 | ~spl3_27 | ~spl3_29),
% 0.22/0.52    inference(avatar_split_clause,[],[f366,f283,f271,f376,f372])).
% 0.22/0.52  fof(f283,plain,(
% 0.22/0.52    spl3_29 <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.52  fof(f366,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | (~spl3_27 | ~spl3_29)),
% 0.22/0.52    inference(subsumption_resolution,[],[f365,f273])).
% 0.22/0.52  fof(f365,plain,(
% 0.22/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl3_29),
% 0.22/0.52    inference(forward_demodulation,[],[f363,f70])).
% 0.22/0.52  fof(f363,plain,(
% 0.22/0.52    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~spl3_29),
% 0.22/0.52    inference(resolution,[],[f285,f74])).
% 0.22/0.52  fof(f285,plain,(
% 0.22/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~spl3_29),
% 0.22/0.52    inference(avatar_component_clause,[],[f283])).
% 0.22/0.52  fof(f340,plain,(
% 0.22/0.52    ~spl3_6 | spl3_8 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f339])).
% 0.22/0.52  fof(f339,plain,(
% 0.22/0.52    $false | (~spl3_6 | spl3_8 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.22/0.52    inference(subsumption_resolution,[],[f338,f126])).
% 0.22/0.52  fof(f338,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f337,f168])).
% 0.22/0.52  fof(f337,plain,(
% 0.22/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl3_6 | ~spl3_13 | ~spl3_15 | ~spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f336,f222])).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK2) | ~spl3_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f220])).
% 0.22/0.52  fof(f333,plain,(
% 0.22/0.52    ~spl3_6 | spl3_9 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f332])).
% 0.22/0.52  fof(f332,plain,(
% 0.22/0.52    $false | (~spl3_6 | spl3_9 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.22/0.52    inference(subsumption_resolution,[],[f331,f130])).
% 0.22/0.52  fof(f130,plain,(
% 0.22/0.52    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f128])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    spl3_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.52  fof(f331,plain,(
% 0.22/0.52    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f330,f168])).
% 0.22/0.52  fof(f330,plain,(
% 0.22/0.52    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | (~spl3_6 | ~spl3_13 | ~spl3_15 | ~spl3_21)),
% 0.22/0.52    inference(forward_demodulation,[],[f329,f222])).
% 0.22/0.52  fof(f329,plain,(
% 0.22/0.52    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl3_6 | ~spl3_13 | ~spl3_15)),
% 0.22/0.52    inference(forward_demodulation,[],[f328,f182])).
% 0.22/0.52  fof(f328,plain,(
% 0.22/0.52    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl3_6 | ~spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f144,f160])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_6),
% 0.22/0.52    inference(resolution,[],[f117,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f286,plain,(
% 0.22/0.52    spl3_29 | ~spl3_11 | ~spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f241,f206,f149,f283])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    spl3_11 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl3_11 | ~spl3_20)),
% 0.22/0.52    inference(superposition,[],[f151,f208])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~spl3_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f149])).
% 0.22/0.52  fof(f279,plain,(
% 0.22/0.52    ~spl3_28 | spl3_9 | ~spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f240,f206,f128,f276])).
% 0.22/0.52  fof(f240,plain,(
% 0.22/0.52    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_9 | ~spl3_20)),
% 0.22/0.52    inference(superposition,[],[f130,f208])).
% 0.22/0.52  fof(f274,plain,(
% 0.22/0.52    spl3_27 | ~spl3_4 | ~spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f243,f206,f101,f271])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_4 | ~spl3_20)),
% 0.22/0.52    inference(forward_demodulation,[],[f237,f70])).
% 0.22/0.52  fof(f237,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl3_4 | ~spl3_20)),
% 0.22/0.52    inference(superposition,[],[f103,f208])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f101])).
% 0.22/0.52  fof(f266,plain,(
% 0.22/0.52    spl3_26 | ~spl3_3 | ~spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f236,f206,f95,f263])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl3_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f236,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl3_3 | ~spl3_20)),
% 0.22/0.52    inference(superposition,[],[f97,f208])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,sK1) | ~spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f95])).
% 0.22/0.52  fof(f223,plain,(
% 0.22/0.52    spl3_21 | ~spl3_4 | ~spl3_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f212,f202,f101,f220])).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    spl3_19 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK2) | (~spl3_4 | ~spl3_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f210,f103])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_19),
% 0.22/0.52    inference(superposition,[],[f204,f61])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f202])).
% 0.22/0.52  fof(f209,plain,(
% 0.22/0.52    spl3_19 | spl3_20 | ~spl3_3 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f191,f101,f95,f206,f202])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl3_3 | ~spl3_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f99,f103])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_3),
% 0.22/0.52    inference(resolution,[],[f97,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    spl3_15 | ~spl3_1 | ~spl3_2 | ~spl3_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f175,f119,f83,f78,f180])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    spl3_7 <=> v1_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_7)),
% 0.22/0.52    inference(subsumption_resolution,[],[f93,f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    v1_relat_1(sK2) | ~spl3_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f119])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f91,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f78])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f85,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f83])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    ~spl3_1 | ~spl3_7 | spl3_13),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f173])).
% 0.22/0.52  fof(f173,plain,(
% 0.22/0.52    $false | (~spl3_1 | ~spl3_7 | spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f172,f120])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | (~spl3_1 | spl3_13)),
% 0.22/0.52    inference(subsumption_resolution,[],[f170,f80])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_13),
% 0.22/0.52    inference(resolution,[],[f161,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    ~v1_relat_1(k2_funct_1(sK2)) | spl3_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f159])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl3_14 | ~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f164,f135,f119,f83,f78,f166])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    spl3_10 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f163,f137])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2) | ~spl3_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f135])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_7)),
% 0.22/0.52    inference(subsumption_resolution,[],[f92,f120])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f90,f80])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f85,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    spl3_11 | ~spl3_1 | ~spl3_7 | ~spl3_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f147,f135,f119,f78,f149])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | (~spl3_1 | ~spl3_7 | ~spl3_10)),
% 0.22/0.52    inference(forward_demodulation,[],[f146,f137])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_7)),
% 0.22/0.52    inference(subsumption_resolution,[],[f88,f120])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f80,f49])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ~spl3_4 | spl3_7),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f139])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    $false | (~spl3_4 | spl3_7)),
% 0.22/0.52    inference(resolution,[],[f132,f103])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_7),
% 0.22/0.52    inference(resolution,[],[f121,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f119])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    spl3_10 | ~spl3_4 | ~spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f112,f106,f101,f135])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    spl3_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f110,f103])).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_5),
% 0.22/0.52    inference(superposition,[],[f108,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f106])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ~spl3_8 | ~spl3_9 | ~spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f37,f115,f128,f124])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f17])).
% 0.22/0.52  fof(f17,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    spl3_6 | ~spl3_7 | ~spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f87,f78,f119,f115])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.22/0.52    inference(resolution,[],[f80,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f42,f106])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f40,f101])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f39,f95])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f41,f83])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v2_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f38,f78])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    v1_funct_1(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (9057)------------------------------
% 0.22/0.52  % (9057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9057)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (9057)Memory used [KB]: 11001
% 0.22/0.52  % (9057)Time elapsed: 0.101 s
% 0.22/0.52  % (9057)------------------------------
% 0.22/0.52  % (9057)------------------------------
% 0.22/0.52  % (9047)Success in time 0.162 s
%------------------------------------------------------------------------------
