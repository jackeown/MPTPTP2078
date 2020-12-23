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
% DateTime   : Thu Dec  3 13:02:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 357 expanded)
%              Number of leaves         :   42 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :  642 (1132 expanded)
%              Number of equality atoms :  128 ( 229 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f752,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f112,f118,f123,f136,f145,f152,f170,f182,f187,f204,f238,f247,f275,f300,f339,f374,f426,f443,f464,f509,f574,f612,f719,f720,f744,f751])).

fof(f751,plain,
    ( spl5_8
    | ~ spl5_21
    | ~ spl5_28
    | ~ spl5_53 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | spl5_8
    | ~ spl5_21
    | ~ spl5_28
    | ~ spl5_53 ),
    inference(subsumption_resolution,[],[f730,f676])).

fof(f676,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f674])).

fof(f674,plain,
    ( spl5_53
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f730,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl5_8
    | ~ spl5_21
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f729,f338])).

fof(f338,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl5_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f729,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl5_8
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f728,f86])).

fof(f86,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f728,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl5_8
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f140,f237])).

fof(f237,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl5_21
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f140,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f744,plain,
    ( ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_28
    | ~ spl5_37
    | ~ spl5_42
    | spl5_53 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_28
    | ~ spl5_37
    | ~ spl5_42
    | spl5_53 ),
    inference(subsumption_resolution,[],[f742,f675])).

fof(f675,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl5_53 ),
    inference(avatar_component_clause,[],[f674])).

fof(f742,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_28
    | ~ spl5_37
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f741,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f741,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_28
    | ~ spl5_37
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f740,f518])).

fof(f518,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f516])).

fof(f516,plain,
    ( spl5_42
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f740,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_28
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f476,f338])).

fof(f476,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f460,f203])).

fof(f203,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl5_16
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f460,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f459,f186])).

fof(f186,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_14
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f459,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl5_6
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f175,f419])).

fof(f419,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f418])).

fof(f418,plain,
    ( spl5_37
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f175,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl5_6 ),
    inference(resolution,[],[f131,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f131,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_6
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f720,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f719,plain,
    ( ~ spl5_30
    | spl5_43
    | ~ spl5_53 ),
    inference(avatar_contradiction_clause,[],[f718])).

fof(f718,plain,
    ( $false
    | ~ spl5_30
    | spl5_43
    | ~ spl5_53 ),
    inference(subsumption_resolution,[],[f717,f350])).

fof(f350,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl5_30
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f717,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | spl5_43
    | ~ spl5_53 ),
    inference(subsumption_resolution,[],[f578,f676])).

fof(f578,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | spl5_43 ),
    inference(forward_demodulation,[],[f577,f86])).

fof(f577,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl5_43 ),
    inference(superposition,[],[f573,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f573,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl5_43 ),
    inference(avatar_component_clause,[],[f571])).

fof(f571,plain,
    ( spl5_43
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f612,plain,
    ( spl5_42
    | ~ spl5_28
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f588,f450,f336,f516])).

fof(f450,plain,
    ( spl5_39
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f588,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_28
    | ~ spl5_39 ),
    inference(forward_demodulation,[],[f451,f338])).

fof(f451,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f450])).

fof(f574,plain,
    ( ~ spl5_43
    | ~ spl5_8
    | spl5_9
    | ~ spl5_21
    | spl5_27
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f569,f336,f295,f235,f142,f138,f571])).

fof(f142,plain,
    ( spl5_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f295,plain,
    ( spl5_27
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f569,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | ~ spl5_8
    | spl5_9
    | ~ spl5_21
    | spl5_27
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f568,f237])).

fof(f568,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(k1_xboole_0))
    | ~ spl5_8
    | spl5_9
    | spl5_27
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f567,f338])).

fof(f567,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl5_8
    | spl5_9
    | spl5_27 ),
    inference(subsumption_resolution,[],[f481,f139])).

fof(f139,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f481,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_9
    | spl5_27 ),
    inference(subsumption_resolution,[],[f480,f297])).

fof(f297,plain,
    ( k1_xboole_0 != sK0
    | spl5_27 ),
    inference(avatar_component_clause,[],[f295])).

fof(f480,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_9 ),
    inference(resolution,[],[f144,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f144,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f509,plain,
    ( ~ spl5_7
    | ~ spl5_23
    | spl5_39 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_23
    | spl5_39 ),
    inference(subsumption_resolution,[],[f507,f452])).

fof(f452,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f450])).

fof(f507,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_7
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f504,f134])).

fof(f134,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f504,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_23 ),
    inference(trivial_inequality_removal,[],[f503])).

fof(f503,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_23 ),
    inference(superposition,[],[f51,f251])).

fof(f251,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl5_23
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f464,plain,
    ( ~ spl5_6
    | spl5_8
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_37 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | ~ spl5_6
    | spl5_8
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f462,f140])).

fof(f462,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f461,f203])).

fof(f461,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_22
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f460,f246])).

fof(f246,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl5_22
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f443,plain,
    ( ~ spl5_6
    | spl5_9
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_37 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl5_6
    | spl5_9
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f441,f144])).

fof(f441,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_37 ),
    inference(forward_demodulation,[],[f440,f246])).

fof(f440,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f209,f419])).

fof(f209,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_6
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f208,f186])).

fof(f208,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f206,f131])).

fof(f206,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_16 ),
    inference(superposition,[],[f56,f203])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f426,plain,
    ( ~ spl5_1
    | ~ spl5_7
    | spl5_37 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_7
    | spl5_37 ),
    inference(subsumption_resolution,[],[f424,f134])).

fof(f424,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_1
    | spl5_37 ),
    inference(subsumption_resolution,[],[f422,f95])).

fof(f95,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f422,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_37 ),
    inference(resolution,[],[f420,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f420,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f418])).

fof(f374,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f339,plain,
    ( spl5_28
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f313,f157,f336])).

fof(f157,plain,
    ( spl5_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f313,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_11 ),
    inference(resolution,[],[f158,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f158,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f300,plain,
    ( k1_xboole_0 != sK1
    | sK1 != k2_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f275,plain,
    ( spl5_13
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl5_13
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f273,f48])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f273,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_13
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f267,f85])).

fof(f267,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl5_13
    | ~ spl5_21 ),
    inference(superposition,[],[f181,f237])).

fof(f181,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_13
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f247,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f241,f231,f115,f244])).

fof(f115,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f231,plain,
    ( spl5_20
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f241,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f239,f117])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f239,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_20 ),
    inference(superposition,[],[f233,f76])).

fof(f233,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f231])).

fof(f238,plain,
    ( spl5_20
    | spl5_21
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f229,f115,f109,f235,f231])).

fof(f109,plain,
    ( spl5_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f229,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f113,f117])).

fof(f113,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(resolution,[],[f111,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f111,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f204,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f199,f149,f133,f98,f93,f201])).

fof(f98,plain,
    ( spl5_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f149,plain,
    ( spl5_10
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f199,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f172,f134])).

fof(f172,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f106,f151])).

fof(f151,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f106,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f104,f95])).

fof(f104,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f100,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f100,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f187,plain,
    ( spl5_14
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f177,f133,f98,f93,f184])).

fof(f177,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f107,f134])).

fof(f107,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f105,f95])).

fof(f105,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f100,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f182,plain,
    ( ~ spl5_13
    | ~ spl5_4
    | spl5_11 ),
    inference(avatar_split_clause,[],[f176,f157,f115,f179])).

fof(f176,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_4
    | spl5_11 ),
    inference(resolution,[],[f165,f117])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | spl5_11 ),
    inference(resolution,[],[f159,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f159,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f170,plain,
    ( ~ spl5_4
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl5_4
    | spl5_7 ),
    inference(resolution,[],[f146,f117])).

fof(f146,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_7 ),
    inference(resolution,[],[f135,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f135,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f152,plain,
    ( spl5_10
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f126,f120,f115,f149])).

fof(f120,plain,
    ( spl5_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f126,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f124,f117])).

fof(f124,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_5 ),
    inference(superposition,[],[f122,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f122,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f145,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f42,f129,f142,f138])).

fof(f42,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f136,plain,
    ( spl5_6
    | ~ spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f102,f93,f133,f129])).

fof(f102,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f95,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f123,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f47,f120])).

fof(f47,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f45,f115])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f112,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f44,f109])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f98])).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f43,f93])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (7757)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (7762)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (7754)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (7759)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (7758)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (7751)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (7756)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (7746)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (7750)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.52  % (7755)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (7749)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (7748)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.53  % (7759)Refutation not found, incomplete strategy% (7759)------------------------------
% 0.20/0.53  % (7759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7749)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (7759)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (7759)Memory used [KB]: 1663
% 0.20/0.54  % (7759)Time elapsed: 0.093 s
% 0.20/0.54  % (7759)------------------------------
% 0.20/0.54  % (7759)------------------------------
% 0.20/0.55  % (7746)Refutation not found, incomplete strategy% (7746)------------------------------
% 0.20/0.55  % (7746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (7746)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (7746)Memory used [KB]: 6652
% 0.20/0.55  % (7746)Time elapsed: 0.092 s
% 0.20/0.55  % (7746)------------------------------
% 0.20/0.55  % (7746)------------------------------
% 0.20/0.55  % (7764)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f752,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f96,f101,f112,f118,f123,f136,f145,f152,f170,f182,f187,f204,f238,f247,f275,f300,f339,f374,f426,f443,f464,f509,f574,f612,f719,f720,f744,f751])).
% 0.20/0.55  fof(f751,plain,(
% 0.20/0.55    spl5_8 | ~spl5_21 | ~spl5_28 | ~spl5_53),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f750])).
% 0.20/0.55  fof(f750,plain,(
% 0.20/0.55    $false | (spl5_8 | ~spl5_21 | ~spl5_28 | ~spl5_53)),
% 0.20/0.55    inference(subsumption_resolution,[],[f730,f676])).
% 0.20/0.55  fof(f676,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl5_53),
% 0.20/0.55    inference(avatar_component_clause,[],[f674])).
% 0.20/0.55  fof(f674,plain,(
% 0.20/0.55    spl5_53 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.20/0.55  fof(f730,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl5_8 | ~spl5_21 | ~spl5_28)),
% 0.20/0.55    inference(forward_demodulation,[],[f729,f338])).
% 0.20/0.55  fof(f338,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | ~spl5_28),
% 0.20/0.55    inference(avatar_component_clause,[],[f336])).
% 0.20/0.55  fof(f336,plain,(
% 0.20/0.55    spl5_28 <=> k1_xboole_0 = sK2),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.20/0.55  fof(f729,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl5_8 | ~spl5_21)),
% 0.20/0.55    inference(forward_demodulation,[],[f728,f86])).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.55  fof(f728,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl5_8 | ~spl5_21)),
% 0.20/0.55    inference(forward_demodulation,[],[f140,f237])).
% 0.20/0.55  fof(f237,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | ~spl5_21),
% 0.20/0.55    inference(avatar_component_clause,[],[f235])).
% 0.20/0.55  fof(f235,plain,(
% 0.20/0.55    spl5_21 <=> k1_xboole_0 = sK1),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.55  fof(f140,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f138])).
% 0.20/0.55  fof(f138,plain,(
% 0.20/0.55    spl5_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.55  fof(f744,plain,(
% 0.20/0.55    ~spl5_6 | ~spl5_14 | ~spl5_16 | ~spl5_28 | ~spl5_37 | ~spl5_42 | spl5_53),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f743])).
% 0.20/0.55  fof(f743,plain,(
% 0.20/0.55    $false | (~spl5_6 | ~spl5_14 | ~spl5_16 | ~spl5_28 | ~spl5_37 | ~spl5_42 | spl5_53)),
% 0.20/0.55    inference(subsumption_resolution,[],[f742,f675])).
% 0.20/0.55  fof(f675,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl5_53),
% 0.20/0.55    inference(avatar_component_clause,[],[f674])).
% 0.20/0.55  fof(f742,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl5_6 | ~spl5_14 | ~spl5_16 | ~spl5_28 | ~spl5_37 | ~spl5_42)),
% 0.20/0.55    inference(forward_demodulation,[],[f741,f85])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f67])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f741,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl5_6 | ~spl5_14 | ~spl5_16 | ~spl5_28 | ~spl5_37 | ~spl5_42)),
% 0.20/0.55    inference(forward_demodulation,[],[f740,f518])).
% 0.20/0.55  fof(f518,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_42),
% 0.20/0.55    inference(avatar_component_clause,[],[f516])).
% 0.20/0.55  fof(f516,plain,(
% 0.20/0.55    spl5_42 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.20/0.55  fof(f740,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)))) | (~spl5_6 | ~spl5_14 | ~spl5_16 | ~spl5_28 | ~spl5_37)),
% 0.20/0.55    inference(forward_demodulation,[],[f476,f338])).
% 0.20/0.55  fof(f476,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl5_6 | ~spl5_14 | ~spl5_16 | ~spl5_37)),
% 0.20/0.55    inference(forward_demodulation,[],[f460,f203])).
% 0.20/0.55  fof(f203,plain,(
% 0.20/0.55    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl5_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f201])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    spl5_16 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.55  fof(f460,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl5_6 | ~spl5_14 | ~spl5_37)),
% 0.20/0.55    inference(forward_demodulation,[],[f459,f186])).
% 0.20/0.55  fof(f186,plain,(
% 0.20/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f184])).
% 0.20/0.55  fof(f184,plain,(
% 0.20/0.55    spl5_14 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.55  fof(f459,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl5_6 | ~spl5_37)),
% 0.20/0.55    inference(subsumption_resolution,[],[f175,f419])).
% 0.20/0.55  fof(f419,plain,(
% 0.20/0.55    v1_relat_1(k2_funct_1(sK2)) | ~spl5_37),
% 0.20/0.55    inference(avatar_component_clause,[],[f418])).
% 0.20/0.55  fof(f418,plain,(
% 0.20/0.55    spl5_37 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.20/0.55  fof(f175,plain,(
% 0.20/0.55    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl5_6),
% 0.20/0.55    inference(resolution,[],[f131,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,axiom,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    v1_funct_1(k2_funct_1(sK2)) | ~spl5_6),
% 0.20/0.55    inference(avatar_component_clause,[],[f129])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    spl5_6 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.55  fof(f720,plain,(
% 0.20/0.55    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relat_1(sK2) | sK0 = k1_relat_1(sK2)),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f719,plain,(
% 0.20/0.55    ~spl5_30 | spl5_43 | ~spl5_53),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f718])).
% 0.20/0.55  fof(f718,plain,(
% 0.20/0.55    $false | (~spl5_30 | spl5_43 | ~spl5_53)),
% 0.20/0.55    inference(subsumption_resolution,[],[f717,f350])).
% 0.20/0.55  fof(f350,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl5_30),
% 0.20/0.55    inference(avatar_component_clause,[],[f348])).
% 0.20/0.55  fof(f348,plain,(
% 0.20/0.55    spl5_30 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.55  fof(f717,plain,(
% 0.20/0.55    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | (spl5_43 | ~spl5_53)),
% 0.20/0.55    inference(subsumption_resolution,[],[f578,f676])).
% 0.20/0.55  fof(f578,plain,(
% 0.20/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | spl5_43),
% 0.20/0.55    inference(forward_demodulation,[],[f577,f86])).
% 0.20/0.55  fof(f577,plain,(
% 0.20/0.55    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl5_43),
% 0.20/0.55    inference(superposition,[],[f573,f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f573,plain,(
% 0.20/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | spl5_43),
% 0.20/0.55    inference(avatar_component_clause,[],[f571])).
% 0.20/0.55  fof(f571,plain,(
% 0.20/0.55    spl5_43 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.20/0.55  fof(f612,plain,(
% 0.20/0.55    spl5_42 | ~spl5_28 | ~spl5_39),
% 0.20/0.55    inference(avatar_split_clause,[],[f588,f450,f336,f516])).
% 0.20/0.55  fof(f450,plain,(
% 0.20/0.55    spl5_39 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.20/0.55  fof(f588,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_28 | ~spl5_39)),
% 0.20/0.55    inference(forward_demodulation,[],[f451,f338])).
% 0.20/0.55  fof(f451,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_39),
% 0.20/0.55    inference(avatar_component_clause,[],[f450])).
% 0.20/0.55  fof(f574,plain,(
% 0.20/0.55    ~spl5_43 | ~spl5_8 | spl5_9 | ~spl5_21 | spl5_27 | ~spl5_28),
% 0.20/0.55    inference(avatar_split_clause,[],[f569,f336,f295,f235,f142,f138,f571])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    spl5_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.55  fof(f295,plain,(
% 0.20/0.55    spl5_27 <=> k1_xboole_0 = sK0),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.20/0.55  fof(f569,plain,(
% 0.20/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (~spl5_8 | spl5_9 | ~spl5_21 | spl5_27 | ~spl5_28)),
% 0.20/0.55    inference(forward_demodulation,[],[f568,f237])).
% 0.20/0.55  fof(f568,plain,(
% 0.20/0.55    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(k1_xboole_0)) | (~spl5_8 | spl5_9 | spl5_27 | ~spl5_28)),
% 0.20/0.55    inference(forward_demodulation,[],[f567,f338])).
% 0.20/0.55  fof(f567,plain,(
% 0.20/0.55    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl5_8 | spl5_9 | spl5_27)),
% 0.20/0.55    inference(subsumption_resolution,[],[f481,f139])).
% 0.20/0.55  fof(f139,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f138])).
% 0.20/0.55  fof(f481,plain,(
% 0.20/0.55    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl5_9 | spl5_27)),
% 0.20/0.55    inference(subsumption_resolution,[],[f480,f297])).
% 0.20/0.55  fof(f297,plain,(
% 0.20/0.55    k1_xboole_0 != sK0 | spl5_27),
% 0.20/0.55    inference(avatar_component_clause,[],[f295])).
% 0.20/0.55  fof(f480,plain,(
% 0.20/0.55    k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_9),
% 0.20/0.55    inference(resolution,[],[f144,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(flattening,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl5_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f142])).
% 0.20/0.55  fof(f509,plain,(
% 0.20/0.55    ~spl5_7 | ~spl5_23 | spl5_39),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f508])).
% 0.20/0.55  fof(f508,plain,(
% 0.20/0.55    $false | (~spl5_7 | ~spl5_23 | spl5_39)),
% 0.20/0.55    inference(subsumption_resolution,[],[f507,f452])).
% 0.20/0.55  fof(f452,plain,(
% 0.20/0.55    k1_xboole_0 != k1_relat_1(sK2) | spl5_39),
% 0.20/0.55    inference(avatar_component_clause,[],[f450])).
% 0.20/0.55  fof(f507,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(sK2) | (~spl5_7 | ~spl5_23)),
% 0.20/0.55    inference(subsumption_resolution,[],[f504,f134])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    v1_relat_1(sK2) | ~spl5_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f133])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    spl5_7 <=> v1_relat_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.55  fof(f504,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~spl5_23),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f503])).
% 0.20/0.55  fof(f503,plain,(
% 0.20/0.55    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~spl5_23),
% 0.20/0.55    inference(superposition,[],[f51,f251])).
% 0.20/0.55  fof(f251,plain,(
% 0.20/0.55    k1_xboole_0 = k2_relat_1(sK2) | ~spl5_23),
% 0.20/0.55    inference(avatar_component_clause,[],[f249])).
% 0.20/0.55  fof(f249,plain,(
% 0.20/0.55    spl5_23 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.55  fof(f464,plain,(
% 0.20/0.55    ~spl5_6 | spl5_8 | ~spl5_14 | ~spl5_16 | ~spl5_22 | ~spl5_37),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f463])).
% 0.20/0.55  fof(f463,plain,(
% 0.20/0.55    $false | (~spl5_6 | spl5_8 | ~spl5_14 | ~spl5_16 | ~spl5_22 | ~spl5_37)),
% 0.20/0.55    inference(subsumption_resolution,[],[f462,f140])).
% 0.20/0.55  fof(f462,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_6 | ~spl5_14 | ~spl5_16 | ~spl5_22 | ~spl5_37)),
% 0.20/0.55    inference(forward_demodulation,[],[f461,f203])).
% 0.20/0.55  fof(f461,plain,(
% 0.20/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | (~spl5_6 | ~spl5_14 | ~spl5_22 | ~spl5_37)),
% 0.20/0.55    inference(forward_demodulation,[],[f460,f246])).
% 0.20/0.55  fof(f246,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK2) | ~spl5_22),
% 0.20/0.55    inference(avatar_component_clause,[],[f244])).
% 0.20/0.55  fof(f244,plain,(
% 0.20/0.55    spl5_22 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.55  fof(f443,plain,(
% 0.20/0.55    ~spl5_6 | spl5_9 | ~spl5_14 | ~spl5_16 | ~spl5_22 | ~spl5_37),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f442])).
% 0.20/0.55  fof(f442,plain,(
% 0.20/0.55    $false | (~spl5_6 | spl5_9 | ~spl5_14 | ~spl5_16 | ~spl5_22 | ~spl5_37)),
% 0.20/0.55    inference(subsumption_resolution,[],[f441,f144])).
% 0.20/0.55  fof(f441,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl5_6 | ~spl5_14 | ~spl5_16 | ~spl5_22 | ~spl5_37)),
% 0.20/0.55    inference(forward_demodulation,[],[f440,f246])).
% 0.20/0.55  fof(f440,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl5_6 | ~spl5_14 | ~spl5_16 | ~spl5_37)),
% 0.20/0.55    inference(subsumption_resolution,[],[f209,f419])).
% 0.20/0.55  fof(f209,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_6 | ~spl5_14 | ~spl5_16)),
% 0.20/0.55    inference(forward_demodulation,[],[f208,f186])).
% 0.20/0.55  fof(f208,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_6 | ~spl5_16)),
% 0.20/0.55    inference(subsumption_resolution,[],[f206,f131])).
% 0.20/0.55  fof(f206,plain,(
% 0.20/0.55    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl5_16),
% 0.20/0.55    inference(superposition,[],[f56,f203])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f426,plain,(
% 0.20/0.55    ~spl5_1 | ~spl5_7 | spl5_37),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f425])).
% 0.20/0.55  fof(f425,plain,(
% 0.20/0.55    $false | (~spl5_1 | ~spl5_7 | spl5_37)),
% 0.20/0.55    inference(subsumption_resolution,[],[f424,f134])).
% 0.20/0.55  fof(f424,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | (~spl5_1 | spl5_37)),
% 0.20/0.55    inference(subsumption_resolution,[],[f422,f95])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    v1_funct_1(sK2) | ~spl5_1),
% 0.20/0.55    inference(avatar_component_clause,[],[f93])).
% 0.20/0.55  fof(f93,plain,(
% 0.20/0.55    spl5_1 <=> v1_funct_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.55  fof(f422,plain,(
% 0.20/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_37),
% 0.20/0.55    inference(resolution,[],[f420,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.55  fof(f420,plain,(
% 0.20/0.55    ~v1_relat_1(k2_funct_1(sK2)) | spl5_37),
% 0.20/0.55    inference(avatar_component_clause,[],[f418])).
% 0.20/0.55  fof(f374,plain,(
% 0.20/0.55    k1_xboole_0 != sK2 | sK1 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f339,plain,(
% 0.20/0.55    spl5_28 | ~spl5_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f313,f157,f336])).
% 0.20/0.55  fof(f157,plain,(
% 0.20/0.55    spl5_11 <=> v1_xboole_0(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.55  fof(f313,plain,(
% 0.20/0.55    k1_xboole_0 = sK2 | ~spl5_11),
% 0.20/0.55    inference(resolution,[],[f158,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.55  fof(f158,plain,(
% 0.20/0.55    v1_xboole_0(sK2) | ~spl5_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f157])).
% 0.20/0.55  fof(f300,plain,(
% 0.20/0.55    k1_xboole_0 != sK1 | sK1 != k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.55  fof(f275,plain,(
% 0.20/0.55    spl5_13 | ~spl5_21),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f274])).
% 0.20/0.55  fof(f274,plain,(
% 0.20/0.55    $false | (spl5_13 | ~spl5_21)),
% 0.20/0.55    inference(subsumption_resolution,[],[f273,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.55  fof(f273,plain,(
% 0.20/0.55    ~v1_xboole_0(k1_xboole_0) | (spl5_13 | ~spl5_21)),
% 0.20/0.55    inference(forward_demodulation,[],[f267,f85])).
% 0.20/0.55  fof(f267,plain,(
% 0.20/0.55    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (spl5_13 | ~spl5_21)),
% 0.20/0.55    inference(superposition,[],[f181,f237])).
% 0.20/0.55  fof(f181,plain,(
% 0.20/0.55    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl5_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f179])).
% 0.20/0.55  fof(f179,plain,(
% 0.20/0.55    spl5_13 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.55  fof(f247,plain,(
% 0.20/0.55    spl5_22 | ~spl5_4 | ~spl5_20),
% 0.20/0.55    inference(avatar_split_clause,[],[f241,f231,f115,f244])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.55  fof(f231,plain,(
% 0.20/0.55    spl5_20 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK2) | (~spl5_4 | ~spl5_20)),
% 0.20/0.55    inference(subsumption_resolution,[],[f239,f117])).
% 0.20/0.55  fof(f117,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f115])).
% 0.20/0.55  fof(f239,plain,(
% 0.20/0.55    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_20),
% 0.20/0.55    inference(superposition,[],[f233,f76])).
% 0.20/0.55  fof(f233,plain,(
% 0.20/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_20),
% 0.20/0.55    inference(avatar_component_clause,[],[f231])).
% 0.20/0.55  fof(f238,plain,(
% 0.20/0.55    spl5_20 | spl5_21 | ~spl5_3 | ~spl5_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f229,f115,f109,f235,f231])).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    spl5_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.55  fof(f229,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl5_3 | ~spl5_4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f113,f117])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_3),
% 0.20/0.55    inference(resolution,[],[f111,f83])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,sK1) | ~spl5_3),
% 0.20/0.55    inference(avatar_component_clause,[],[f109])).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    spl5_16 | ~spl5_1 | ~spl5_2 | ~spl5_7 | ~spl5_10),
% 0.20/0.55    inference(avatar_split_clause,[],[f199,f149,f133,f98,f93,f201])).
% 0.20/0.55  fof(f98,plain,(
% 0.20/0.55    spl5_2 <=> v2_funct_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.55  fof(f149,plain,(
% 0.20/0.55    spl5_10 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_7 | ~spl5_10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f172,f134])).
% 0.20/0.55  fof(f172,plain,(
% 0.20/0.55    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl5_1 | ~spl5_2 | ~spl5_10)),
% 0.20/0.55    inference(forward_demodulation,[],[f106,f151])).
% 0.20/0.55  fof(f151,plain,(
% 0.20/0.55    sK1 = k2_relat_1(sK2) | ~spl5_10),
% 0.20/0.55    inference(avatar_component_clause,[],[f149])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f104,f95])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl5_2),
% 0.20/0.55    inference(resolution,[],[f100,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    v2_funct_1(sK2) | ~spl5_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f98])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    spl5_14 | ~spl5_1 | ~spl5_2 | ~spl5_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f177,f133,f98,f93,f184])).
% 0.20/0.55  fof(f177,plain,(
% 0.20/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_7)),
% 0.20/0.55    inference(subsumption_resolution,[],[f107,f134])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f105,f95])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_2),
% 0.20/0.55    inference(resolution,[],[f100,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f33])).
% 0.20/0.55  fof(f182,plain,(
% 0.20/0.55    ~spl5_13 | ~spl5_4 | spl5_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f176,f157,f115,f179])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | (~spl5_4 | spl5_11)),
% 0.20/0.55    inference(resolution,[],[f165,f117])).
% 0.20/0.55  fof(f165,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | spl5_11),
% 0.20/0.55    inference(resolution,[],[f159,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.55  fof(f159,plain,(
% 0.20/0.55    ~v1_xboole_0(sK2) | spl5_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f157])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    ~spl5_4 | spl5_7),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f167])).
% 0.20/0.55  fof(f167,plain,(
% 0.20/0.55    $false | (~spl5_4 | spl5_7)),
% 0.20/0.55    inference(resolution,[],[f146,f117])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_7),
% 0.20/0.55    inference(resolution,[],[f135,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | spl5_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f133])).
% 0.20/0.55  fof(f152,plain,(
% 0.20/0.55    spl5_10 | ~spl5_4 | ~spl5_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f126,f120,f115,f149])).
% 0.20/0.55  fof(f120,plain,(
% 0.20/0.55    spl5_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    sK1 = k2_relat_1(sK2) | (~spl5_4 | ~spl5_5)),
% 0.20/0.55    inference(subsumption_resolution,[],[f124,f117])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_5),
% 0.20/0.55    inference(superposition,[],[f122,f77])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.55  fof(f122,plain,(
% 0.20/0.55    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl5_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f120])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    ~spl5_8 | ~spl5_9 | ~spl5_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f42,f129,f142,f138])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.55    inference(negated_conjecture,[],[f20])).
% 0.20/0.55  fof(f20,conjecture,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    spl5_6 | ~spl5_7 | ~spl5_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f102,f93,f133,f129])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl5_1),
% 0.20/0.55    inference(resolution,[],[f95,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    spl5_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f47,f120])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    spl5_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f45,f115])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    spl5_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f44,f109])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    spl5_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f46,f98])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    v2_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    spl5_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f43,f93])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    v1_funct_1(sK2)),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (7749)------------------------------
% 0.20/0.55  % (7749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (7749)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (7749)Memory used [KB]: 10874
% 0.20/0.55  % (7749)Time elapsed: 0.104 s
% 0.20/0.55  % (7749)------------------------------
% 0.20/0.55  % (7749)------------------------------
% 0.20/0.55  % (7744)Success in time 0.19 s
%------------------------------------------------------------------------------
