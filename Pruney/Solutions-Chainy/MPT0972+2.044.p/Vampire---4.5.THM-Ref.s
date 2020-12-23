%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 484 expanded)
%              Number of leaves         :   44 ( 196 expanded)
%              Depth                    :   13
%              Number of atoms          :  731 (1739 expanded)
%              Number of equality atoms :  166 ( 484 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f980,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f88,f93,f102,f107,f112,f135,f159,f164,f191,f228,f281,f381,f413,f415,f499,f518,f527,f534,f545,f553,f576,f585,f632,f639,f690,f693,f697,f778,f799,f800,f870,f890,f970,f972,f979])).

fof(f979,plain,
    ( ~ spl7_4
    | ~ spl7_7
    | spl7_15
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f978])).

fof(f978,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_7
    | spl7_15
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f977,f256])).

fof(f256,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl7_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f977,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_4
    | ~ spl7_7
    | spl7_15
    | ~ spl7_20
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f976,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f976,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_4
    | ~ spl7_7
    | spl7_15
    | ~ spl7_20
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f973,f960])).

fof(f960,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_4
    | ~ spl7_7
    | spl7_15
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f315,f280])).

fof(f280,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl7_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f315,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl7_4
    | ~ spl7_7
    | spl7_15 ),
    inference(backward_demodulation,[],[f189,f310])).

fof(f310,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4
    | ~ spl7_7
    | spl7_15 ),
    inference(subsumption_resolution,[],[f289,f189])).

fof(f289,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f261,f111])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f261,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(resolution,[],[f92,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f92,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f189,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl7_15
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f973,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_24 ),
    inference(resolution,[],[f412,f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f412,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl7_24
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f972,plain,
    ( spl7_24
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f947,f278,f132,f90,f410])).

fof(f132,plain,
    ( spl7_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f947,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f137,f280])).

fof(f137,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f92,f134])).

fof(f134,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f970,plain,
    ( spl7_18
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f146,f132,f109,f254])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f140,f63])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f111,f134])).

fof(f890,plain,
    ( spl7_11
    | ~ spl7_4
    | ~ spl7_7
    | spl7_15 ),
    inference(avatar_split_clause,[],[f310,f188,f109,f90,f132])).

fof(f870,plain,
    ( spl7_16
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f145,f132,f104,f216])).

fof(f216,plain,
    ( spl7_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f104,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f145,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f139,f63])).

fof(f139,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f106,f134])).

fof(f106,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f800,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f799,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f778,plain,
    ( ~ spl7_7
    | ~ spl7_11
    | ~ spl7_13
    | spl7_20
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f777])).

fof(f777,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_13
    | spl7_20
    | spl7_31 ),
    inference(subsumption_resolution,[],[f764,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f764,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_13
    | spl7_20
    | spl7_31 ),
    inference(backward_demodulation,[],[f544,f755])).

fof(f755,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_13
    | spl7_20 ),
    inference(subsumption_resolution,[],[f193,f279])).

fof(f279,plain,
    ( k1_xboole_0 != sK0
    | spl7_20 ),
    inference(avatar_component_clause,[],[f278])).

fof(f193,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f178,f146])).

fof(f178,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f176,f63])).

fof(f176,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_13 ),
    inference(resolution,[],[f163,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f163,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_13
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f544,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl7_31 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl7_31
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f697,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f693,plain,
    ( ~ spl7_7
    | spl7_46 ),
    inference(avatar_contradiction_clause,[],[f692])).

fof(f692,plain,
    ( $false
    | ~ spl7_7
    | spl7_46 ),
    inference(subsumption_resolution,[],[f691,f111])).

fof(f691,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_46 ),
    inference(resolution,[],[f689,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f689,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | spl7_46 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl7_46
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f690,plain,
    ( ~ spl7_46
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_32
    | ~ spl7_34
    | spl7_45 ),
    inference(avatar_split_clause,[],[f649,f636,f556,f547,f285,f225,f99,f78,f73,f687])).

fof(f73,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f78,plain,
    ( spl7_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f99,plain,
    ( spl7_5
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f225,plain,
    ( spl7_17
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f285,plain,
    ( spl7_21
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f547,plain,
    ( spl7_32
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f556,plain,
    ( spl7_34
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f636,plain,
    ( spl7_45
  <=> r2_hidden(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f649,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_5
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_32
    | ~ spl7_34
    | spl7_45 ),
    inference(backward_demodulation,[],[f101,f646])).

fof(f646,plain,
    ( sK2 = sK3
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_32
    | ~ spl7_34
    | spl7_45 ),
    inference(subsumption_resolution,[],[f645,f287])).

fof(f287,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f285])).

fof(f645,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_17
    | ~ spl7_32
    | ~ spl7_34
    | spl7_45 ),
    inference(subsumption_resolution,[],[f644,f80])).

fof(f80,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f644,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl7_1
    | ~ spl7_17
    | ~ spl7_32
    | ~ spl7_34
    | spl7_45 ),
    inference(subsumption_resolution,[],[f643,f557])).

fof(f557,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f556])).

% (758)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f643,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl7_1
    | ~ spl7_17
    | ~ spl7_32
    | spl7_45 ),
    inference(resolution,[],[f577,f638])).

fof(f638,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | spl7_45 ),
    inference(avatar_component_clause,[],[f636])).

fof(f577,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | sK3 = X0 )
    | ~ spl7_1
    | ~ spl7_17
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f264,f548])).

fof(f548,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f547])).

fof(f264,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK3)
        | sK3 = X0 )
    | ~ spl7_1
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f263,f75])).

% (741)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f75,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f263,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK3)
        | sK3 = X0 )
    | ~ spl7_17 ),
    inference(superposition,[],[f36,f227])).

fof(f227,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f225])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
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
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f101,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f639,plain,
    ( ~ spl7_45
    | spl7_44 ),
    inference(avatar_split_clause,[],[f634,f629,f636])).

fof(f629,plain,
    ( spl7_44
  <=> k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f634,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | spl7_44 ),
    inference(trivial_inequality_removal,[],[f633])).

fof(f633,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ r2_hidden(sK4(sK3,sK2),sK0)
    | spl7_44 ),
    inference(superposition,[],[f631,f26])).

fof(f26,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f631,plain,
    ( k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | spl7_44 ),
    inference(avatar_component_clause,[],[f629])).

fof(f632,plain,
    ( ~ spl7_44
    | spl7_39
    | ~ spl7_2
    | ~ spl7_21
    | ~ spl7_33
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f587,f556,f551,f285,f78,f603,f629])).

fof(f603,plain,
    ( spl7_39
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f551,plain,
    ( spl7_33
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK3 = X0
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f587,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ spl7_2
    | ~ spl7_21
    | ~ spl7_33
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f586,f557])).

fof(f586,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_2
    | ~ spl7_21
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f578,f287])).

fof(f578,plain,
    ( sK2 = sK3
    | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_2
    | ~ spl7_33 ),
    inference(resolution,[],[f552,f80])).

fof(f552,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK3 = X0
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f551])).

fof(f585,plain,
    ( ~ spl7_7
    | spl7_34 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl7_7
    | spl7_34 ),
    inference(subsumption_resolution,[],[f582,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f582,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_7
    | spl7_34 ),
    inference(resolution,[],[f563,f111])).

fof(f563,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_34 ),
    inference(resolution,[],[f558,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f558,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_34 ),
    inference(avatar_component_clause,[],[f556])).

fof(f576,plain,
    ( ~ spl7_6
    | spl7_32 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | ~ spl7_6
    | spl7_32 ),
    inference(subsumption_resolution,[],[f573,f40])).

fof(f573,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_6
    | spl7_32 ),
    inference(resolution,[],[f554,f106])).

fof(f554,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_32 ),
    inference(resolution,[],[f549,f35])).

fof(f549,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_32 ),
    inference(avatar_component_clause,[],[f547])).

fof(f553,plain,
    ( ~ spl7_32
    | spl7_33
    | ~ spl7_1
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f258,f225,f73,f551,f547])).

fof(f258,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | sK3 = X0 )
    | ~ spl7_1
    | ~ spl7_17 ),
    inference(backward_demodulation,[],[f82,f227])).

% (741)Refutation not found, incomplete strategy% (741)------------------------------
% (741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (741)Termination reason: Refutation not found, incomplete strategy

% (741)Memory used [KB]: 10746
% (741)Time elapsed: 0.161 s
% (741)------------------------------
% (741)------------------------------
fof(f82,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK3)
        | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0))
        | sK3 = X0 )
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f545,plain,
    ( spl7_30
    | ~ spl7_31
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f505,f496,f542,f538])).

fof(f538,plain,
    ( spl7_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f496,plain,
    ( spl7_27
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f505,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_27 ),
    inference(resolution,[],[f498,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f498,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f496])).

fof(f534,plain,
    ( spl7_29
    | ~ spl7_16
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f485,f378,f216,f531])).

fof(f531,plain,
    ( spl7_29
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f378,plain,
    ( spl7_23
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f485,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_23 ),
    inference(forward_demodulation,[],[f482,f63])).

fof(f482,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_23 ),
    inference(resolution,[],[f380,f65])).

% (751)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f380,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f378])).

fof(f527,plain,
    ( spl7_10
    | ~ spl7_3
    | ~ spl7_6
    | spl7_11 ),
    inference(avatar_split_clause,[],[f259,f132,f104,f85,f128])).

fof(f128,plain,
    ( spl7_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f85,plain,
    ( spl7_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f259,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_3
    | ~ spl7_6
    | spl7_11 ),
    inference(subsumption_resolution,[],[f229,f133])).

fof(f133,plain,
    ( k1_xboole_0 != sK1
    | spl7_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f229,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f221,f106])).

fof(f221,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(resolution,[],[f87,f58])).

fof(f87,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f518,plain,
    ( spl7_21
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f271,f188,f109,f285])).

fof(f271,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_7
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f269,f111])).

fof(f269,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_15 ),
    inference(superposition,[],[f190,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f190,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f499,plain,
    ( spl7_27
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f375,f254,f496])).

fof(f375,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_18 ),
    inference(resolution,[],[f256,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

% (755)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f415,plain,
    ( spl7_23
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f382,f278,f156,f378])).

% (760)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f156,plain,
    ( spl7_12
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f382,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f158,f280])).

fof(f158,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f413,plain,
    ( spl7_24
    | ~ spl7_13
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f362,f278,f161,f410])).

fof(f362,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl7_13
    | ~ spl7_20 ),
    inference(backward_demodulation,[],[f163,f280])).

fof(f381,plain,
    ( spl7_23
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f360,f278,f132,f85,f378])).

fof(f360,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(backward_demodulation,[],[f136,f280])).

fof(f136,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(backward_demodulation,[],[f87,f134])).

fof(f281,plain,
    ( spl7_19
    | spl7_20
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f230,f216,f156,f278,f274])).

fof(f274,plain,
    ( spl7_19
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f230,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f175,f218])).

fof(f218,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f216])).

fof(f175,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f173,f63])).

fof(f173,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_12 ),
    inference(resolution,[],[f158,f67])).

fof(f228,plain,
    ( spl7_17
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f185,f128,f104,f225])).

fof(f185,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f183,f106])).

fof(f183,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_10 ),
    inference(superposition,[],[f130,f52])).

fof(f130,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f191,plain,
    ( spl7_15
    | ~ spl7_4
    | spl7_11 ),
    inference(avatar_split_clause,[],[f170,f132,f90,f188])).

fof(f170,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_4
    | spl7_11 ),
    inference(subsumption_resolution,[],[f97,f133])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f96,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(resolution,[],[f92,f58])).

fof(f164,plain,
    ( spl7_13
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f137,f132,f90,f161])).

fof(f159,plain,
    ( spl7_12
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f136,f132,f85,f156])).

fof(f135,plain,
    ( spl7_10
    | spl7_11
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f95,f85,f132,f128])).

fof(f95,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f94,f29])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(resolution,[],[f87,f58])).

fof(f112,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f33,f109])).

fof(f107,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f29,f104])).

fof(f102,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f30,f99])).

fof(f30,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f28,f85])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f27,f73])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (753)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (744)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (731)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (730)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (761)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (759)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (739)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (753)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (733)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (749)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (750)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f980,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f76,f81,f88,f93,f102,f107,f112,f135,f159,f164,f191,f228,f281,f381,f413,f415,f499,f518,f527,f534,f545,f553,f576,f585,f632,f639,f690,f693,f697,f778,f799,f800,f870,f890,f970,f972,f979])).
% 0.21/0.56  fof(f979,plain,(
% 0.21/0.56    ~spl7_4 | ~spl7_7 | spl7_15 | ~spl7_18 | ~spl7_20 | ~spl7_24),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f978])).
% 0.21/0.56  fof(f978,plain,(
% 0.21/0.56    $false | (~spl7_4 | ~spl7_7 | spl7_15 | ~spl7_18 | ~spl7_20 | ~spl7_24)),
% 0.21/0.56    inference(subsumption_resolution,[],[f977,f256])).
% 0.21/0.56  fof(f256,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl7_18),
% 0.21/0.56    inference(avatar_component_clause,[],[f254])).
% 0.21/0.56  fof(f254,plain,(
% 0.21/0.56    spl7_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.56  fof(f977,plain,(
% 0.21/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_4 | ~spl7_7 | spl7_15 | ~spl7_20 | ~spl7_24)),
% 0.21/0.56    inference(forward_demodulation,[],[f976,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.56  fof(f976,plain,(
% 0.21/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_4 | ~spl7_7 | spl7_15 | ~spl7_20 | ~spl7_24)),
% 0.21/0.56    inference(subsumption_resolution,[],[f973,f960])).
% 0.21/0.56  fof(f960,plain,(
% 0.21/0.56    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl7_4 | ~spl7_7 | spl7_15 | ~spl7_20)),
% 0.21/0.56    inference(forward_demodulation,[],[f315,f280])).
% 0.21/0.56  fof(f280,plain,(
% 0.21/0.56    k1_xboole_0 = sK0 | ~spl7_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f278])).
% 0.21/0.56  fof(f278,plain,(
% 0.21/0.56    spl7_20 <=> k1_xboole_0 = sK0),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.56  fof(f315,plain,(
% 0.21/0.56    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (~spl7_4 | ~spl7_7 | spl7_15)),
% 0.21/0.56    inference(backward_demodulation,[],[f189,f310])).
% 0.21/0.56  fof(f310,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | (~spl7_4 | ~spl7_7 | spl7_15)),
% 0.21/0.56    inference(subsumption_resolution,[],[f289,f189])).
% 0.21/0.56  fof(f289,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl7_4 | ~spl7_7)),
% 0.21/0.56    inference(subsumption_resolution,[],[f261,f111])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    spl7_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.56  fof(f261,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_4),
% 0.21/0.56    inference(resolution,[],[f92,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    v1_funct_2(sK2,sK0,sK1) | ~spl7_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f90])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    spl7_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.56  fof(f189,plain,(
% 0.21/0.56    sK0 != k1_relset_1(sK0,sK1,sK2) | spl7_15),
% 0.21/0.56    inference(avatar_component_clause,[],[f188])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    spl7_15 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.56  fof(f973,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_24),
% 0.21/0.56    inference(resolution,[],[f412,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.56    inference(equality_resolution,[],[f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f412,plain,(
% 0.21/0.56    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl7_24),
% 0.21/0.56    inference(avatar_component_clause,[],[f410])).
% 0.21/0.56  fof(f410,plain,(
% 0.21/0.56    spl7_24 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.56  fof(f972,plain,(
% 0.21/0.56    spl7_24 | ~spl7_4 | ~spl7_11 | ~spl7_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f947,f278,f132,f90,f410])).
% 0.21/0.56  fof(f132,plain,(
% 0.21/0.56    spl7_11 <=> k1_xboole_0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.56  fof(f947,plain,(
% 0.21/0.56    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_4 | ~spl7_11 | ~spl7_20)),
% 0.21/0.56    inference(forward_demodulation,[],[f137,f280])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl7_4 | ~spl7_11)),
% 0.21/0.56    inference(backward_demodulation,[],[f92,f134])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | ~spl7_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f132])).
% 0.21/0.56  fof(f970,plain,(
% 0.21/0.56    spl7_18 | ~spl7_7 | ~spl7_11),
% 0.21/0.56    inference(avatar_split_clause,[],[f146,f132,f109,f254])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl7_7 | ~spl7_11)),
% 0.21/0.56    inference(forward_demodulation,[],[f140,f63])).
% 0.21/0.56  fof(f140,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_7 | ~spl7_11)),
% 0.21/0.56    inference(backward_demodulation,[],[f111,f134])).
% 0.21/0.56  fof(f890,plain,(
% 0.21/0.56    spl7_11 | ~spl7_4 | ~spl7_7 | spl7_15),
% 0.21/0.56    inference(avatar_split_clause,[],[f310,f188,f109,f90,f132])).
% 0.21/0.56  fof(f870,plain,(
% 0.21/0.56    spl7_16 | ~spl7_6 | ~spl7_11),
% 0.21/0.56    inference(avatar_split_clause,[],[f145,f132,f104,f216])).
% 0.21/0.56  fof(f216,plain,(
% 0.21/0.56    spl7_16 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    spl7_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.56  fof(f145,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl7_6 | ~spl7_11)),
% 0.21/0.56    inference(forward_demodulation,[],[f139,f63])).
% 0.21/0.56  fof(f139,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_6 | ~spl7_11)),
% 0.21/0.56    inference(backward_demodulation,[],[f106,f134])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f104])).
% 0.21/0.56  fof(f800,plain,(
% 0.21/0.56    k1_xboole_0 != sK1 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f799,plain,(
% 0.21/0.56    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f778,plain,(
% 0.21/0.56    ~spl7_7 | ~spl7_11 | ~spl7_13 | spl7_20 | spl7_31),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f777])).
% 0.21/0.56  fof(f777,plain,(
% 0.21/0.56    $false | (~spl7_7 | ~spl7_11 | ~spl7_13 | spl7_20 | spl7_31)),
% 0.21/0.56    inference(subsumption_resolution,[],[f764,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f764,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_7 | ~spl7_11 | ~spl7_13 | spl7_20 | spl7_31)),
% 0.21/0.56    inference(backward_demodulation,[],[f544,f755])).
% 0.21/0.56  fof(f755,plain,(
% 0.21/0.56    k1_xboole_0 = sK2 | (~spl7_7 | ~spl7_11 | ~spl7_13 | spl7_20)),
% 0.21/0.56    inference(subsumption_resolution,[],[f193,f279])).
% 0.21/0.56  fof(f279,plain,(
% 0.21/0.56    k1_xboole_0 != sK0 | spl7_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f278])).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl7_7 | ~spl7_11 | ~spl7_13)),
% 0.21/0.56    inference(subsumption_resolution,[],[f178,f146])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl7_13),
% 0.21/0.56    inference(forward_demodulation,[],[f176,f63])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_13),
% 0.21/0.56    inference(resolution,[],[f163,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.21/0.56    inference(equality_resolution,[],[f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f163,plain,(
% 0.21/0.56    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl7_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f161])).
% 0.21/0.56  fof(f161,plain,(
% 0.21/0.56    spl7_13 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.56  fof(f544,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK2) | spl7_31),
% 0.21/0.56    inference(avatar_component_clause,[],[f542])).
% 0.21/0.56  fof(f542,plain,(
% 0.21/0.56    spl7_31 <=> r1_tarski(k1_xboole_0,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.56  fof(f697,plain,(
% 0.21/0.56    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.56  fof(f693,plain,(
% 0.21/0.56    ~spl7_7 | spl7_46),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f692])).
% 0.21/0.56  fof(f692,plain,(
% 0.21/0.56    $false | (~spl7_7 | spl7_46)),
% 0.21/0.56    inference(subsumption_resolution,[],[f691,f111])).
% 0.21/0.56  fof(f691,plain,(
% 0.21/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl7_46),
% 0.21/0.56    inference(resolution,[],[f689,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.56    inference(equality_resolution,[],[f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.56  fof(f689,plain,(
% 0.21/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | spl7_46),
% 0.21/0.56    inference(avatar_component_clause,[],[f687])).
% 0.21/0.56  fof(f687,plain,(
% 0.21/0.56    spl7_46 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.21/0.56  fof(f690,plain,(
% 0.21/0.56    ~spl7_46 | ~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_17 | ~spl7_21 | ~spl7_32 | ~spl7_34 | spl7_45),
% 0.21/0.56    inference(avatar_split_clause,[],[f649,f636,f556,f547,f285,f225,f99,f78,f73,f687])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    spl7_1 <=> v1_funct_1(sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    spl7_2 <=> v1_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    spl7_5 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.56  fof(f225,plain,(
% 0.21/0.56    spl7_17 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.56  fof(f285,plain,(
% 0.21/0.56    spl7_21 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.56  fof(f547,plain,(
% 0.21/0.56    spl7_32 <=> v1_relat_1(sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.56  fof(f556,plain,(
% 0.21/0.56    spl7_34 <=> v1_relat_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.56  fof(f636,plain,(
% 0.21/0.56    spl7_45 <=> r2_hidden(sK4(sK3,sK2),sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.21/0.56  fof(f649,plain,(
% 0.21/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | (~spl7_1 | ~spl7_2 | spl7_5 | ~spl7_17 | ~spl7_21 | ~spl7_32 | ~spl7_34 | spl7_45)),
% 0.21/0.56    inference(backward_demodulation,[],[f101,f646])).
% 0.21/0.56  fof(f646,plain,(
% 0.21/0.56    sK2 = sK3 | (~spl7_1 | ~spl7_2 | ~spl7_17 | ~spl7_21 | ~spl7_32 | ~spl7_34 | spl7_45)),
% 0.21/0.56    inference(subsumption_resolution,[],[f645,f287])).
% 0.21/0.56  fof(f287,plain,(
% 0.21/0.56    sK0 = k1_relat_1(sK2) | ~spl7_21),
% 0.21/0.56    inference(avatar_component_clause,[],[f285])).
% 0.21/0.56  fof(f645,plain,(
% 0.21/0.56    sK0 != k1_relat_1(sK2) | sK2 = sK3 | (~spl7_1 | ~spl7_2 | ~spl7_17 | ~spl7_32 | ~spl7_34 | spl7_45)),
% 0.21/0.56    inference(subsumption_resolution,[],[f644,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    v1_funct_1(sK2) | ~spl7_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f78])).
% 0.21/0.56  fof(f644,plain,(
% 0.21/0.56    ~v1_funct_1(sK2) | sK0 != k1_relat_1(sK2) | sK2 = sK3 | (~spl7_1 | ~spl7_17 | ~spl7_32 | ~spl7_34 | spl7_45)),
% 0.21/0.56    inference(subsumption_resolution,[],[f643,f557])).
% 0.21/0.56  fof(f557,plain,(
% 0.21/0.56    v1_relat_1(sK2) | ~spl7_34),
% 0.21/0.56    inference(avatar_component_clause,[],[f556])).
% 0.21/0.56  % (758)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  fof(f643,plain,(
% 0.21/0.56    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK0 != k1_relat_1(sK2) | sK2 = sK3 | (~spl7_1 | ~spl7_17 | ~spl7_32 | spl7_45)),
% 0.21/0.56    inference(resolution,[],[f577,f638])).
% 0.21/0.56  fof(f638,plain,(
% 0.21/0.56    ~r2_hidden(sK4(sK3,sK2),sK0) | spl7_45),
% 0.21/0.56    inference(avatar_component_clause,[],[f636])).
% 0.21/0.56  fof(f577,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | sK3 = X0) ) | (~spl7_1 | ~spl7_17 | ~spl7_32)),
% 0.21/0.56    inference(subsumption_resolution,[],[f264,f548])).
% 0.21/0.56  fof(f548,plain,(
% 0.21/0.56    v1_relat_1(sK3) | ~spl7_32),
% 0.21/0.56    inference(avatar_component_clause,[],[f547])).
% 0.21/0.56  fof(f264,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0) ) | (~spl7_1 | ~spl7_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f263,f75])).
% 0.21/0.56  % (741)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    v1_funct_1(sK3) | ~spl7_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f73])).
% 0.21/0.56  fof(f263,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0) ) | ~spl7_17),
% 0.21/0.56    inference(superposition,[],[f36,f227])).
% 0.21/0.56  fof(f227,plain,(
% 0.21/0.56    sK0 = k1_relat_1(sK3) | ~spl7_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f225])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ~r2_relset_1(sK0,sK1,sK2,sK3) | spl7_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f99])).
% 0.21/0.56  fof(f639,plain,(
% 0.21/0.56    ~spl7_45 | spl7_44),
% 0.21/0.56    inference(avatar_split_clause,[],[f634,f629,f636])).
% 0.21/0.56  fof(f629,plain,(
% 0.21/0.56    spl7_44 <=> k1_funct_1(sK3,sK4(sK3,sK2)) = k1_funct_1(sK2,sK4(sK3,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.56  fof(f634,plain,(
% 0.21/0.56    ~r2_hidden(sK4(sK3,sK2),sK0) | spl7_44),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f633])).
% 0.21/0.56  fof(f633,plain,(
% 0.21/0.56    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~r2_hidden(sK4(sK3,sK2),sK0) | spl7_44),
% 0.21/0.56    inference(superposition,[],[f631,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.56    inference(negated_conjecture,[],[f13])).
% 0.21/0.56  fof(f13,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 0.21/0.56  fof(f631,plain,(
% 0.21/0.56    k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | spl7_44),
% 0.21/0.56    inference(avatar_component_clause,[],[f629])).
% 0.21/0.56  fof(f632,plain,(
% 0.21/0.56    ~spl7_44 | spl7_39 | ~spl7_2 | ~spl7_21 | ~spl7_33 | ~spl7_34),
% 0.21/0.56    inference(avatar_split_clause,[],[f587,f556,f551,f285,f78,f603,f629])).
% 0.21/0.56  fof(f603,plain,(
% 0.21/0.56    spl7_39 <=> sK2 = sK3),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.56  fof(f551,plain,(
% 0.21/0.56    spl7_33 <=> ! [X0] : (k1_relat_1(X0) != sK0 | sK3 = X0 | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.56  fof(f587,plain,(
% 0.21/0.56    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | (~spl7_2 | ~spl7_21 | ~spl7_33 | ~spl7_34)),
% 0.21/0.56    inference(subsumption_resolution,[],[f586,f557])).
% 0.21/0.56  fof(f586,plain,(
% 0.21/0.56    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | ~v1_relat_1(sK2) | (~spl7_2 | ~spl7_21 | ~spl7_33)),
% 0.21/0.56    inference(subsumption_resolution,[],[f578,f287])).
% 0.21/0.56  fof(f578,plain,(
% 0.21/0.56    sK2 = sK3 | k1_funct_1(sK3,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl7_2 | ~spl7_33)),
% 0.21/0.56    inference(resolution,[],[f552,f80])).
% 0.21/0.56  fof(f552,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_funct_1(X0) | sK3 = X0 | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | k1_relat_1(X0) != sK0 | ~v1_relat_1(X0)) ) | ~spl7_33),
% 0.21/0.56    inference(avatar_component_clause,[],[f551])).
% 0.21/0.56  fof(f585,plain,(
% 0.21/0.56    ~spl7_7 | spl7_34),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f584])).
% 0.21/0.56  fof(f584,plain,(
% 0.21/0.56    $false | (~spl7_7 | spl7_34)),
% 0.21/0.56    inference(subsumption_resolution,[],[f582,f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.56  fof(f582,plain,(
% 0.21/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_7 | spl7_34)),
% 0.21/0.56    inference(resolution,[],[f563,f111])).
% 0.21/0.56  fof(f563,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_34),
% 0.21/0.56    inference(resolution,[],[f558,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.56  fof(f558,plain,(
% 0.21/0.56    ~v1_relat_1(sK2) | spl7_34),
% 0.21/0.56    inference(avatar_component_clause,[],[f556])).
% 0.21/0.56  fof(f576,plain,(
% 0.21/0.56    ~spl7_6 | spl7_32),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f575])).
% 0.21/0.56  fof(f575,plain,(
% 0.21/0.56    $false | (~spl7_6 | spl7_32)),
% 0.21/0.56    inference(subsumption_resolution,[],[f573,f40])).
% 0.21/0.56  fof(f573,plain,(
% 0.21/0.56    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_6 | spl7_32)),
% 0.21/0.56    inference(resolution,[],[f554,f106])).
% 0.21/0.56  fof(f554,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_32),
% 0.21/0.56    inference(resolution,[],[f549,f35])).
% 0.21/0.56  fof(f549,plain,(
% 0.21/0.56    ~v1_relat_1(sK3) | spl7_32),
% 0.21/0.56    inference(avatar_component_clause,[],[f547])).
% 0.21/0.56  fof(f553,plain,(
% 0.21/0.56    ~spl7_32 | spl7_33 | ~spl7_1 | ~spl7_17),
% 0.21/0.56    inference(avatar_split_clause,[],[f258,f225,f73,f551,f547])).
% 0.21/0.56  fof(f258,plain,(
% 0.21/0.56    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0) ) | (~spl7_1 | ~spl7_17)),
% 0.21/0.56    inference(backward_demodulation,[],[f82,f227])).
% 0.21/0.57  % (741)Refutation not found, incomplete strategy% (741)------------------------------
% 0.21/0.57  % (741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (741)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (741)Memory used [KB]: 10746
% 0.21/0.57  % (741)Time elapsed: 0.161 s
% 0.21/0.57  % (741)------------------------------
% 0.21/0.57  % (741)------------------------------
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | k1_funct_1(sK3,sK4(sK3,X0)) != k1_funct_1(X0,sK4(sK3,X0)) | sK3 = X0) ) | ~spl7_1),
% 0.21/0.57    inference(resolution,[],[f75,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f545,plain,(
% 0.21/0.57    spl7_30 | ~spl7_31 | ~spl7_27),
% 0.21/0.57    inference(avatar_split_clause,[],[f505,f496,f542,f538])).
% 0.21/0.57  fof(f538,plain,(
% 0.21/0.57    spl7_30 <=> k1_xboole_0 = sK2),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.57  fof(f496,plain,(
% 0.21/0.57    spl7_27 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.57  fof(f505,plain,(
% 0.21/0.57    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2 | ~spl7_27),
% 0.21/0.57    inference(resolution,[],[f498,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f498,plain,(
% 0.21/0.57    r1_tarski(sK2,k1_xboole_0) | ~spl7_27),
% 0.21/0.57    inference(avatar_component_clause,[],[f496])).
% 0.21/0.57  fof(f534,plain,(
% 0.21/0.57    spl7_29 | ~spl7_16 | ~spl7_23),
% 0.21/0.57    inference(avatar_split_clause,[],[f485,f378,f216,f531])).
% 0.21/0.57  fof(f531,plain,(
% 0.21/0.57    spl7_29 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.57  fof(f378,plain,(
% 0.21/0.57    spl7_23 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.57  fof(f485,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~spl7_23),
% 0.21/0.57    inference(forward_demodulation,[],[f482,f63])).
% 0.21/0.57  fof(f482,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_23),
% 0.21/0.57    inference(resolution,[],[f380,f65])).
% 0.21/0.57  % (751)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  fof(f380,plain,(
% 0.21/0.57    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl7_23),
% 0.21/0.57    inference(avatar_component_clause,[],[f378])).
% 0.21/0.57  fof(f527,plain,(
% 0.21/0.57    spl7_10 | ~spl7_3 | ~spl7_6 | spl7_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f259,f132,f104,f85,f128])).
% 0.21/0.57  fof(f128,plain,(
% 0.21/0.57    spl7_10 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    spl7_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.57  fof(f259,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl7_3 | ~spl7_6 | spl7_11)),
% 0.21/0.57    inference(subsumption_resolution,[],[f229,f133])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    k1_xboole_0 != sK1 | spl7_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f132])).
% 0.21/0.57  fof(f229,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl7_3 | ~spl7_6)),
% 0.21/0.57    inference(subsumption_resolution,[],[f221,f106])).
% 0.21/0.57  fof(f221,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.21/0.57    inference(resolution,[],[f87,f58])).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    v1_funct_2(sK3,sK0,sK1) | ~spl7_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f85])).
% 0.21/0.57  fof(f518,plain,(
% 0.21/0.57    spl7_21 | ~spl7_7 | ~spl7_15),
% 0.21/0.57    inference(avatar_split_clause,[],[f271,f188,f109,f285])).
% 0.21/0.57  fof(f271,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK2) | (~spl7_7 | ~spl7_15)),
% 0.21/0.57    inference(subsumption_resolution,[],[f269,f111])).
% 0.21/0.57  fof(f269,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_15),
% 0.21/0.57    inference(superposition,[],[f190,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.57  fof(f190,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_15),
% 0.21/0.57    inference(avatar_component_clause,[],[f188])).
% 0.21/0.57  fof(f499,plain,(
% 0.21/0.57    spl7_27 | ~spl7_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f375,f254,f496])).
% 0.21/0.57  fof(f375,plain,(
% 0.21/0.57    r1_tarski(sK2,k1_xboole_0) | ~spl7_18),
% 0.21/0.57    inference(resolution,[],[f256,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  % (755)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  fof(f415,plain,(
% 0.21/0.57    spl7_23 | ~spl7_12 | ~spl7_20),
% 0.21/0.57    inference(avatar_split_clause,[],[f382,f278,f156,f378])).
% 0.21/0.57  % (760)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    spl7_12 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.57  fof(f382,plain,(
% 0.21/0.57    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_12 | ~spl7_20)),
% 0.21/0.57    inference(forward_demodulation,[],[f158,f280])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl7_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f156])).
% 0.21/0.57  fof(f413,plain,(
% 0.21/0.57    spl7_24 | ~spl7_13 | ~spl7_20),
% 0.21/0.57    inference(avatar_split_clause,[],[f362,f278,f161,f410])).
% 0.21/0.57  fof(f362,plain,(
% 0.21/0.57    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl7_13 | ~spl7_20)),
% 0.21/0.57    inference(backward_demodulation,[],[f163,f280])).
% 0.21/0.57  fof(f381,plain,(
% 0.21/0.57    spl7_23 | ~spl7_3 | ~spl7_11 | ~spl7_20),
% 0.21/0.57    inference(avatar_split_clause,[],[f360,f278,f132,f85,f378])).
% 0.21/0.57  fof(f360,plain,(
% 0.21/0.57    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl7_3 | ~spl7_11 | ~spl7_20)),
% 0.21/0.57    inference(backward_demodulation,[],[f136,f280])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl7_3 | ~spl7_11)),
% 0.21/0.57    inference(backward_demodulation,[],[f87,f134])).
% 0.21/0.57  fof(f281,plain,(
% 0.21/0.57    spl7_19 | spl7_20 | ~spl7_12 | ~spl7_16),
% 0.21/0.57    inference(avatar_split_clause,[],[f230,f216,f156,f278,f274])).
% 0.21/0.57  fof(f274,plain,(
% 0.21/0.57    spl7_19 <=> k1_xboole_0 = sK3),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.57  fof(f230,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | (~spl7_12 | ~spl7_16)),
% 0.21/0.57    inference(subsumption_resolution,[],[f175,f218])).
% 0.21/0.57  fof(f218,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_16),
% 0.21/0.57    inference(avatar_component_clause,[],[f216])).
% 0.21/0.57  fof(f175,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~spl7_12),
% 0.21/0.57    inference(forward_demodulation,[],[f173,f63])).
% 0.21/0.57  fof(f173,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_12),
% 0.21/0.57    inference(resolution,[],[f158,f67])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    spl7_17 | ~spl7_6 | ~spl7_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f185,f128,f104,f225])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK3) | (~spl7_6 | ~spl7_10)),
% 0.21/0.57    inference(subsumption_resolution,[],[f183,f106])).
% 0.21/0.57  fof(f183,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_10),
% 0.21/0.57    inference(superposition,[],[f130,f52])).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f128])).
% 0.21/0.57  fof(f191,plain,(
% 0.21/0.57    spl7_15 | ~spl7_4 | spl7_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f170,f132,f90,f188])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl7_4 | spl7_11)),
% 0.21/0.57    inference(subsumption_resolution,[],[f97,f133])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_4),
% 0.21/0.57    inference(subsumption_resolution,[],[f96,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_4),
% 0.21/0.57    inference(resolution,[],[f92,f58])).
% 0.21/0.57  fof(f164,plain,(
% 0.21/0.57    spl7_13 | ~spl7_4 | ~spl7_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f137,f132,f90,f161])).
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    spl7_12 | ~spl7_3 | ~spl7_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f136,f132,f85,f156])).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    spl7_10 | spl7_11 | ~spl7_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f95,f85,f132,f128])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f94,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.21/0.57    inference(resolution,[],[f87,f58])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    spl7_7),
% 0.21/0.57    inference(avatar_split_clause,[],[f33,f109])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    spl7_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f29,f104])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ~spl7_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f30,f99])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    spl7_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f32,f90])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    spl7_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f28,f85])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    spl7_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f31,f78])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    v1_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    spl7_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f27,f73])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    v1_funct_1(sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f16])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (753)------------------------------
% 0.21/0.57  % (753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (753)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (753)Memory used [KB]: 11257
% 0.21/0.57  % (753)Time elapsed: 0.137 s
% 0.21/0.57  % (753)------------------------------
% 0.21/0.57  % (753)------------------------------
% 0.21/0.57  % (746)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (734)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (728)Success in time 0.208 s
%------------------------------------------------------------------------------
