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
% DateTime   : Thu Dec  3 13:02:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 417 expanded)
%              Number of leaves         :   40 ( 163 expanded)
%              Depth                    :   13
%              Number of atoms          :  666 (1318 expanded)
%              Number of equality atoms :  129 ( 309 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f699,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f93,f99,f104,f117,f126,f133,f137,f147,f164,f169,f178,f204,f218,f261,f269,f274,f281,f328,f335,f374,f407,f428,f500,f541,f639,f670,f685,f687,f698])).

fof(f698,plain,
    ( ~ spl3_59
    | spl3_8
    | ~ spl3_20
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f652,f367,f201,f119,f626])).

fof(f626,plain,
    ( spl3_59
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f119,plain,
    ( spl3_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f201,plain,
    ( spl3_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f367,plain,
    ( spl3_32
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f652,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl3_8
    | ~ spl3_20
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f651,f369])).

fof(f369,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f367])).

fof(f651,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_8
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f650,f66])).

fof(f66,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f650,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_8
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f121,f203])).

fof(f203,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f121,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f687,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f685,plain,
    ( ~ spl3_32
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f684])).

% (6315)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f684,plain,
    ( $false
    | ~ spl3_32
    | spl3_33 ),
    inference(subsumption_resolution,[],[f683,f41])).

fof(f41,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f683,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl3_32
    | spl3_33 ),
    inference(forward_demodulation,[],[f372,f369])).

fof(f372,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl3_33
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f670,plain,
    ( ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_32
    | spl3_59 ),
    inference(avatar_contradiction_clause,[],[f669])).

fof(f669,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_32
    | spl3_59 ),
    inference(subsumption_resolution,[],[f668,f627])).

fof(f627,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl3_59 ),
    inference(avatar_component_clause,[],[f626])).

fof(f668,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f667,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f667,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f666,f41])).

fof(f666,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f337,f369])).

fof(f337,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f331,f163])).

fof(f163,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_14
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f331,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f330,f177])).

fof(f177,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_15
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f330,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f140,f155])).

fof(f155,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_13
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f140,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_6 ),
    inference(resolution,[],[f112,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f112,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_6
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f639,plain,
    ( ~ spl3_40
    | spl3_48
    | ~ spl3_59 ),
    inference(avatar_contradiction_clause,[],[f638])).

fof(f638,plain,
    ( $false
    | ~ spl3_40
    | spl3_48
    | ~ spl3_59 ),
    inference(subsumption_resolution,[],[f549,f628])).

fof(f628,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f626])).

fof(f549,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_40
    | spl3_48 ),
    inference(forward_demodulation,[],[f548,f66])).

fof(f548,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl3_40
    | spl3_48 ),
    inference(subsumption_resolution,[],[f547,f436])).

fof(f436,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl3_40
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f547,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_48 ),
    inference(superposition,[],[f540,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f540,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl3_48 ),
    inference(avatar_component_clause,[],[f538])).

fof(f538,plain,
    ( spl3_48
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f541,plain,
    ( ~ spl3_48
    | spl3_28
    | ~ spl3_31
    | ~ spl3_32
    | spl3_36 ),
    inference(avatar_split_clause,[],[f535,f404,f367,f352,f271,f538])).

fof(f271,plain,
    ( spl3_28
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f352,plain,
    ( spl3_31
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f404,plain,
    ( spl3_36
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f535,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl3_28
    | ~ spl3_31
    | ~ spl3_32
    | spl3_36 ),
    inference(forward_demodulation,[],[f534,f369])).

fof(f534,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl3_28
    | ~ spl3_31
    | spl3_36 ),
    inference(subsumption_resolution,[],[f533,f406])).

fof(f406,plain,
    ( k1_xboole_0 != sK0
    | spl3_36 ),
    inference(avatar_component_clause,[],[f404])).

fof(f533,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl3_28
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f276,f354])).

fof(f354,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f352])).

fof(f276,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl3_28 ),
    inference(forward_demodulation,[],[f275,f66])).

fof(f275,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_28 ),
    inference(resolution,[],[f273,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f273,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f271])).

fof(f500,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f428,plain,
    ( ~ spl3_26
    | ~ spl3_27
    | spl3_32
    | spl3_36 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl3_26
    | ~ spl3_27
    | spl3_32
    | spl3_36 ),
    inference(subsumption_resolution,[],[f426,f368])).

fof(f368,plain,
    ( k1_xboole_0 != sK2
    | spl3_32 ),
    inference(avatar_component_clause,[],[f367])).

fof(f426,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_26
    | ~ spl3_27
    | spl3_36 ),
    inference(subsumption_resolution,[],[f425,f406])).

fof(f425,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_26
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f264,f268])).

fof(f268,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl3_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f264,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f262,f65])).

fof(f262,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_26 ),
    inference(resolution,[],[f260,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f260,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl3_26
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f407,plain,
    ( ~ spl3_36
    | spl3_21
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f393,f371,f215,f404])).

fof(f215,plain,
    ( spl3_21
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f393,plain,
    ( k1_xboole_0 != sK0
    | spl3_21
    | ~ spl3_33 ),
    inference(superposition,[],[f216,f373])).

fof(f373,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f371])).

fof(f216,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f215])).

fof(f374,plain,
    ( spl3_32
    | spl3_33
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f361,f278,f266,f371,f367])).

fof(f278,plain,
    ( spl3_29
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f361,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f360,f268])).

fof(f360,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f358,f65])).

fof(f358,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_29 ),
    inference(resolution,[],[f280,f69])).

fof(f280,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f278])).

fof(f335,plain,
    ( ~ spl3_6
    | spl3_8
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | ~ spl3_6
    | spl3_8
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f333,f121])).

fof(f333,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f332,f163])).

fof(f332,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f331,f217])).

fof(f217,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f215])).

fof(f328,plain,
    ( ~ spl3_6
    | spl3_9
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl3_6
    | spl3_9
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f326,f125])).

fof(f125,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f326,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f325,f163])).

fof(f325,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f324,f217])).

fof(f324,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f323,f177])).

fof(f323,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f139,f155])).

fof(f139,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_6 ),
    inference(resolution,[],[f112,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f281,plain,
    ( spl3_29
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f236,f201,f144,f278])).

fof(f144,plain,
    ( spl3_11
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f236,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(superposition,[],[f146,f203])).

fof(f146,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f274,plain,
    ( ~ spl3_28
    | spl3_9
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f235,f201,f123,f271])).

fof(f235,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_9
    | ~ spl3_20 ),
    inference(superposition,[],[f125,f203])).

fof(f269,plain,
    ( spl3_27
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f238,f201,f96,f266])).

fof(f96,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f238,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f232,f65])).

fof(f232,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(superposition,[],[f98,f203])).

fof(f98,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f261,plain,
    ( spl3_26
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f231,f201,f90,f258])).

fof(f90,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

% (6303)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f231,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(superposition,[],[f92,f203])).

fof(f92,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f218,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f207,f197,f96,f215])).

fof(f197,plain,
    ( spl3_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f207,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f205,f98])).

fof(f205,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_19 ),
    inference(superposition,[],[f199,f56])).

fof(f199,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f197])).

fof(f204,plain,
    ( spl3_19
    | spl3_20
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f186,f96,f90,f201,f197])).

fof(f186,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f94,f98])).

fof(f94,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(resolution,[],[f92,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f178,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f170,f114,f78,f73,f175])).

fof(f73,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f78,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f114,plain,
    ( spl3_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f170,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f88,f115])).

fof(f115,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f86,f75])).

fof(f75,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f86,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f80,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f80,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f169,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7
    | spl3_13 ),
    inference(subsumption_resolution,[],[f167,f115])).

fof(f167,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_13 ),
    inference(subsumption_resolution,[],[f165,f75])).

fof(f165,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_13 ),
    inference(resolution,[],[f156,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f156,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f164,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f159,f130,f114,f78,f73,f161])).

fof(f130,plain,
    ( spl3_10
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f159,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f158,f132])).

fof(f132,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f158,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f87,f115])).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f85,f75])).

fof(f85,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f80,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f147,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f142,f130,f114,f73,f144])).

fof(f142,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f141,f132])).

fof(f141,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f83,f115])).

fof(f83,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f75,f44])).

fof(f137,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl3_4
    | spl3_7 ),
    inference(resolution,[],[f127,f98])).

fof(f127,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_7 ),
    inference(resolution,[],[f116,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f116,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f133,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f107,f101,f96,f130])).

fof(f101,plain,
    ( spl3_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f107,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f105,f98])).

fof(f105,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_5 ),
    inference(superposition,[],[f103,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f103,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f126,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f34,f110,f123,f119])).

fof(f34,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f117,plain,
    ( spl3_6
    | ~ spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f82,f73,f114,f110])).

fof(f82,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f39,f101])).

fof(f39,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f37,f96])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f93,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:40 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.20/0.47  % (6301)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (6318)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (6318)Refutation not found, incomplete strategy% (6318)------------------------------
% 0.20/0.49  % (6318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6318)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (6318)Memory used [KB]: 10618
% 0.20/0.49  % (6318)Time elapsed: 0.071 s
% 0.20/0.49  % (6318)------------------------------
% 0.20/0.49  % (6318)------------------------------
% 0.20/0.49  % (6312)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (6302)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (6299)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (6300)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (6297)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (6310)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (6306)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (6298)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (6298)Refutation not found, incomplete strategy% (6298)------------------------------
% 0.20/0.50  % (6298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6298)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6298)Memory used [KB]: 10618
% 0.20/0.50  % (6298)Time elapsed: 0.093 s
% 0.20/0.50  % (6298)------------------------------
% 0.20/0.50  % (6298)------------------------------
% 0.20/0.51  % (6316)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (6313)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (6300)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f699,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f76,f81,f93,f99,f104,f117,f126,f133,f137,f147,f164,f169,f178,f204,f218,f261,f269,f274,f281,f328,f335,f374,f407,f428,f500,f541,f639,f670,f685,f687,f698])).
% 0.20/0.51  fof(f698,plain,(
% 0.20/0.51    ~spl3_59 | spl3_8 | ~spl3_20 | ~spl3_32),
% 0.20/0.51    inference(avatar_split_clause,[],[f652,f367,f201,f119,f626])).
% 0.20/0.51  fof(f626,plain,(
% 0.20/0.51    spl3_59 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl3_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    spl3_20 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.51  fof(f367,plain,(
% 0.20/0.51    spl3_32 <=> k1_xboole_0 = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.51  fof(f652,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl3_8 | ~spl3_20 | ~spl3_32)),
% 0.20/0.51    inference(forward_demodulation,[],[f651,f369])).
% 0.20/0.51  fof(f369,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~spl3_32),
% 0.20/0.51    inference(avatar_component_clause,[],[f367])).
% 0.20/0.51  fof(f651,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl3_8 | ~spl3_20)),
% 0.20/0.51    inference(forward_demodulation,[],[f650,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f650,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_8 | ~spl3_20)),
% 0.20/0.51    inference(forward_demodulation,[],[f121,f203])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl3_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f201])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f119])).
% 0.20/0.51  fof(f687,plain,(
% 0.20/0.51    k1_xboole_0 != sK2 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f685,plain,(
% 0.20/0.51    ~spl3_32 | spl3_33),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f684])).
% 0.20/0.51  % (6315)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  fof(f684,plain,(
% 0.20/0.51    $false | (~spl3_32 | spl3_33)),
% 0.20/0.51    inference(subsumption_resolution,[],[f683,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.51  fof(f683,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl3_32 | spl3_33)),
% 0.20/0.51    inference(forward_demodulation,[],[f372,f369])).
% 0.20/0.51  fof(f372,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relat_1(sK2) | spl3_33),
% 0.20/0.51    inference(avatar_component_clause,[],[f371])).
% 0.20/0.51  fof(f371,plain,(
% 0.20/0.51    spl3_33 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.51  fof(f670,plain,(
% 0.20/0.51    ~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_32 | spl3_59),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f669])).
% 0.20/0.51  fof(f669,plain,(
% 0.20/0.51    $false | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_32 | spl3_59)),
% 0.20/0.51    inference(subsumption_resolution,[],[f668,f627])).
% 0.20/0.51  fof(f627,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl3_59),
% 0.20/0.51    inference(avatar_component_clause,[],[f626])).
% 0.20/0.51  fof(f668,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_32)),
% 0.20/0.51    inference(forward_demodulation,[],[f667,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f667,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_32)),
% 0.20/0.51    inference(forward_demodulation,[],[f666,f41])).
% 0.20/0.51  fof(f666,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)))) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_32)),
% 0.20/0.51    inference(forward_demodulation,[],[f337,f369])).
% 0.20/0.51  fof(f337,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15)),
% 0.20/0.51    inference(forward_demodulation,[],[f331,f163])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f161])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    spl3_14 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.51  fof(f331,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl3_6 | ~spl3_13 | ~spl3_15)),
% 0.20/0.51    inference(forward_demodulation,[],[f330,f177])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f175])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    spl3_15 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.51  fof(f330,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl3_6 | ~spl3_13)),
% 0.20/0.51    inference(subsumption_resolution,[],[f140,f155])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    v1_relat_1(k2_funct_1(sK2)) | ~spl3_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f154])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    spl3_13 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_6),
% 0.20/0.51    inference(resolution,[],[f112,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    v1_funct_1(k2_funct_1(sK2)) | ~spl3_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl3_6 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.51  fof(f639,plain,(
% 0.20/0.51    ~spl3_40 | spl3_48 | ~spl3_59),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f638])).
% 0.20/0.51  fof(f638,plain,(
% 0.20/0.51    $false | (~spl3_40 | spl3_48 | ~spl3_59)),
% 0.20/0.51    inference(subsumption_resolution,[],[f549,f628])).
% 0.20/0.51  fof(f628,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_59),
% 0.20/0.51    inference(avatar_component_clause,[],[f626])).
% 0.20/0.51  fof(f549,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl3_40 | spl3_48)),
% 0.20/0.51    inference(forward_demodulation,[],[f548,f66])).
% 0.20/0.51  fof(f548,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl3_40 | spl3_48)),
% 0.20/0.51    inference(subsumption_resolution,[],[f547,f436])).
% 0.20/0.51  fof(f436,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_40),
% 0.20/0.51    inference(avatar_component_clause,[],[f434])).
% 0.20/0.51  fof(f434,plain,(
% 0.20/0.51    spl3_40 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.51  fof(f547,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_48),
% 0.20/0.51    inference(superposition,[],[f540,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f540,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | spl3_48),
% 0.20/0.51    inference(avatar_component_clause,[],[f538])).
% 0.20/0.51  fof(f538,plain,(
% 0.20/0.51    spl3_48 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.51  fof(f541,plain,(
% 0.20/0.51    ~spl3_48 | spl3_28 | ~spl3_31 | ~spl3_32 | spl3_36),
% 0.20/0.51    inference(avatar_split_clause,[],[f535,f404,f367,f352,f271,f538])).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    spl3_28 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.51  fof(f352,plain,(
% 0.20/0.51    spl3_31 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.51  fof(f404,plain,(
% 0.20/0.51    spl3_36 <=> k1_xboole_0 = sK0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.51  fof(f535,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (spl3_28 | ~spl3_31 | ~spl3_32 | spl3_36)),
% 0.20/0.51    inference(forward_demodulation,[],[f534,f369])).
% 0.20/0.51  fof(f534,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl3_28 | ~spl3_31 | spl3_36)),
% 0.20/0.51    inference(subsumption_resolution,[],[f533,f406])).
% 0.20/0.51  fof(f406,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 | spl3_36),
% 0.20/0.51    inference(avatar_component_clause,[],[f404])).
% 0.20/0.51  fof(f533,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (spl3_28 | ~spl3_31)),
% 0.20/0.51    inference(subsumption_resolution,[],[f276,f354])).
% 0.20/0.51  fof(f354,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~spl3_31),
% 0.20/0.51    inference(avatar_component_clause,[],[f352])).
% 0.20/0.51  fof(f276,plain,(
% 0.20/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | spl3_28),
% 0.20/0.51    inference(forward_demodulation,[],[f275,f66])).
% 0.20/0.51  fof(f275,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl3_28),
% 0.20/0.51    inference(resolution,[],[f273,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.51  fof(f273,plain,(
% 0.20/0.51    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | spl3_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f271])).
% 0.20/0.51  fof(f500,plain,(
% 0.20/0.51    k1_xboole_0 != sK2 | sK1 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f428,plain,(
% 0.20/0.51    ~spl3_26 | ~spl3_27 | spl3_32 | spl3_36),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f427])).
% 0.20/0.51  fof(f427,plain,(
% 0.20/0.51    $false | (~spl3_26 | ~spl3_27 | spl3_32 | spl3_36)),
% 0.20/0.51    inference(subsumption_resolution,[],[f426,f368])).
% 0.20/0.51  fof(f368,plain,(
% 0.20/0.51    k1_xboole_0 != sK2 | spl3_32),
% 0.20/0.51    inference(avatar_component_clause,[],[f367])).
% 0.20/0.51  fof(f426,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | (~spl3_26 | ~spl3_27 | spl3_36)),
% 0.20/0.51    inference(subsumption_resolution,[],[f425,f406])).
% 0.20/0.51  fof(f425,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl3_26 | ~spl3_27)),
% 0.20/0.51    inference(subsumption_resolution,[],[f264,f268])).
% 0.20/0.51  fof(f268,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f266])).
% 0.20/0.51  fof(f266,plain,(
% 0.20/0.51    spl3_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.51  fof(f264,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl3_26),
% 0.20/0.51    inference(forward_demodulation,[],[f262,f65])).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_26),
% 0.20/0.51    inference(resolution,[],[f260,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f260,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl3_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f258])).
% 0.20/0.51  fof(f258,plain,(
% 0.20/0.51    spl3_26 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.51  fof(f407,plain,(
% 0.20/0.51    ~spl3_36 | spl3_21 | ~spl3_33),
% 0.20/0.51    inference(avatar_split_clause,[],[f393,f371,f215,f404])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    spl3_21 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.51  fof(f393,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 | (spl3_21 | ~spl3_33)),
% 0.20/0.51    inference(superposition,[],[f216,f373])).
% 0.20/0.51  fof(f373,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_33),
% 0.20/0.51    inference(avatar_component_clause,[],[f371])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    sK0 != k1_relat_1(sK2) | spl3_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f215])).
% 0.20/0.51  fof(f374,plain,(
% 0.20/0.51    spl3_32 | spl3_33 | ~spl3_27 | ~spl3_29),
% 0.20/0.51    inference(avatar_split_clause,[],[f361,f278,f266,f371,f367])).
% 0.20/0.51  fof(f278,plain,(
% 0.20/0.51    spl3_29 <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.51  fof(f361,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | (~spl3_27 | ~spl3_29)),
% 0.20/0.51    inference(subsumption_resolution,[],[f360,f268])).
% 0.20/0.51  fof(f360,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl3_29),
% 0.20/0.51    inference(forward_demodulation,[],[f358,f65])).
% 0.20/0.51  fof(f358,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~spl3_29),
% 0.20/0.51    inference(resolution,[],[f280,f69])).
% 0.20/0.51  fof(f280,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~spl3_29),
% 0.20/0.51    inference(avatar_component_clause,[],[f278])).
% 0.20/0.51  fof(f335,plain,(
% 0.20/0.51    ~spl3_6 | spl3_8 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f334])).
% 0.20/0.51  fof(f334,plain,(
% 0.20/0.51    $false | (~spl3_6 | spl3_8 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f333,f121])).
% 0.20/0.51  fof(f333,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.20/0.51    inference(forward_demodulation,[],[f332,f163])).
% 0.20/0.51  fof(f332,plain,(
% 0.20/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl3_6 | ~spl3_13 | ~spl3_15 | ~spl3_21)),
% 0.20/0.51    inference(forward_demodulation,[],[f331,f217])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK2) | ~spl3_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f215])).
% 0.20/0.51  fof(f328,plain,(
% 0.20/0.51    ~spl3_6 | spl3_9 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f327])).
% 0.20/0.51  fof(f327,plain,(
% 0.20/0.51    $false | (~spl3_6 | spl3_9 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.20/0.51    inference(subsumption_resolution,[],[f326,f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    spl3_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.51  fof(f326,plain,(
% 0.20/0.51    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_6 | ~spl3_13 | ~spl3_14 | ~spl3_15 | ~spl3_21)),
% 0.20/0.51    inference(forward_demodulation,[],[f325,f163])).
% 0.20/0.51  fof(f325,plain,(
% 0.20/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | (~spl3_6 | ~spl3_13 | ~spl3_15 | ~spl3_21)),
% 0.20/0.51    inference(forward_demodulation,[],[f324,f217])).
% 0.20/0.51  fof(f324,plain,(
% 0.20/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl3_6 | ~spl3_13 | ~spl3_15)),
% 0.20/0.51    inference(forward_demodulation,[],[f323,f177])).
% 0.20/0.51  fof(f323,plain,(
% 0.20/0.51    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl3_6 | ~spl3_13)),
% 0.20/0.51    inference(subsumption_resolution,[],[f139,f155])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_6),
% 0.20/0.51    inference(resolution,[],[f112,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f281,plain,(
% 0.20/0.51    spl3_29 | ~spl3_11 | ~spl3_20),
% 0.20/0.51    inference(avatar_split_clause,[],[f236,f201,f144,f278])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    spl3_11 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl3_11 | ~spl3_20)),
% 0.20/0.51    inference(superposition,[],[f146,f203])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~spl3_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f144])).
% 0.20/0.51  fof(f274,plain,(
% 0.20/0.51    ~spl3_28 | spl3_9 | ~spl3_20),
% 0.20/0.51    inference(avatar_split_clause,[],[f235,f201,f123,f271])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_9 | ~spl3_20)),
% 0.20/0.51    inference(superposition,[],[f125,f203])).
% 0.20/0.51  fof(f269,plain,(
% 0.20/0.51    spl3_27 | ~spl3_4 | ~spl3_20),
% 0.20/0.51    inference(avatar_split_clause,[],[f238,f201,f96,f266])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_4 | ~spl3_20)),
% 0.20/0.51    inference(forward_demodulation,[],[f232,f65])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl3_4 | ~spl3_20)),
% 0.20/0.51    inference(superposition,[],[f98,f203])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f96])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    spl3_26 | ~spl3_3 | ~spl3_20),
% 0.20/0.51    inference(avatar_split_clause,[],[f231,f201,f90,f258])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl3_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.51  % (6303)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl3_3 | ~spl3_20)),
% 0.20/0.51    inference(superposition,[],[f92,f203])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    spl3_21 | ~spl3_4 | ~spl3_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f207,f197,f96,f215])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    spl3_19 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK2) | (~spl3_4 | ~spl3_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f205,f98])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_19),
% 0.20/0.51    inference(superposition,[],[f199,f56])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f197])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    spl3_19 | spl3_20 | ~spl3_3 | ~spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f186,f96,f90,f201,f197])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl3_3 | ~spl3_4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f94,f98])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_3),
% 0.20/0.51    inference(resolution,[],[f92,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    spl3_15 | ~spl3_1 | ~spl3_2 | ~spl3_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f170,f114,f78,f73,f175])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl3_1 <=> v1_funct_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl3_2 <=> v2_funct_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl3_7 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f88,f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl3_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f114])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f86,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    v1_funct_1(sK2) | ~spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f73])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f80,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    v2_funct_1(sK2) | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f78])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    ~spl3_1 | ~spl3_7 | spl3_13),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    $false | (~spl3_1 | ~spl3_7 | spl3_13)),
% 0.20/0.51    inference(subsumption_resolution,[],[f167,f115])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | (~spl3_1 | spl3_13)),
% 0.20/0.51    inference(subsumption_resolution,[],[f165,f75])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_13),
% 0.20/0.51    inference(resolution,[],[f156,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    ~v1_relat_1(k2_funct_1(sK2)) | spl3_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f154])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    spl3_14 | ~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f159,f130,f114,f78,f73,f161])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    spl3_10 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_7 | ~spl3_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f158,f132])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    sK1 = k2_relat_1(sK2) | ~spl3_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f130])).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f87,f115])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f85,f75])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f80,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    spl3_11 | ~spl3_1 | ~spl3_7 | ~spl3_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f142,f130,f114,f73,f144])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | (~spl3_1 | ~spl3_7 | ~spl3_10)),
% 0.20/0.51    inference(forward_demodulation,[],[f141,f132])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f83,f115])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_1),
% 0.20/0.51    inference(resolution,[],[f75,f44])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ~spl3_4 | spl3_7),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f134])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    $false | (~spl3_4 | spl3_7)),
% 0.20/0.51    inference(resolution,[],[f127,f98])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_7),
% 0.20/0.51    inference(resolution,[],[f116,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | spl3_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f114])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl3_10 | ~spl3_4 | ~spl3_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f107,f101,f96,f130])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    spl3_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    sK1 = k2_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.20/0.51    inference(subsumption_resolution,[],[f105,f98])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_5),
% 0.20/0.51    inference(superposition,[],[f103,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f101])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ~spl3_8 | ~spl3_9 | ~spl3_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f34,f110,f123,f119])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f15])).
% 0.20/0.51  fof(f15,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    spl3_6 | ~spl3_7 | ~spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f82,f73,f114,f110])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.20/0.51    inference(resolution,[],[f75,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl3_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f101])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f37,f96])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f36,f90])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f78])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    v2_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f73])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (6300)------------------------------
% 0.20/0.51  % (6300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6300)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (6300)Memory used [KB]: 10874
% 0.20/0.51  % (6300)Time elapsed: 0.100 s
% 0.20/0.51  % (6300)------------------------------
% 0.20/0.51  % (6300)------------------------------
% 0.20/0.51  % (6296)Success in time 0.151 s
%------------------------------------------------------------------------------
