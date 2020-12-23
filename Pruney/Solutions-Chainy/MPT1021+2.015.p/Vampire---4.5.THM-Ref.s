%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:52 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 335 expanded)
%              Number of leaves         :   49 ( 158 expanded)
%              Depth                    :    8
%              Number of atoms          :  595 (1000 expanded)
%              Number of equality atoms :   84 ( 134 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f918,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f136,f145,f155,f165,f172,f177,f186,f195,f202,f241,f260,f270,f275,f295,f302,f374,f549,f559,f604,f611,f616,f711,f764,f768,f806,f912,f917])).

fof(f917,plain,(
    spl2_76 ),
    inference(avatar_contradiction_clause,[],[f913])).

fof(f913,plain,
    ( $false
    | spl2_76 ),
    inference(unit_resulting_resolution,[],[f47,f911])).

fof(f911,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl2_76 ),
    inference(avatar_component_clause,[],[f909])).

fof(f909,plain,
    ( spl2_76
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f912,plain,
    ( ~ spl2_76
    | ~ spl2_17
    | spl2_18
    | ~ spl2_59 ),
    inference(avatar_split_clause,[],[f858,f803,f199,f192,f909])).

fof(f192,plain,
    ( spl2_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f199,plain,
    ( spl2_18
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f803,plain,
    ( spl2_59
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f858,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl2_17
    | spl2_18
    | ~ spl2_59 ),
    inference(forward_demodulation,[],[f759,f805])).

fof(f805,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_59 ),
    inference(avatar_component_clause,[],[f803])).

fof(f759,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | ~ spl2_17
    | spl2_18 ),
    inference(forward_demodulation,[],[f200,f194])).

fof(f194,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f192])).

fof(f200,plain,
    ( sK0 != k1_relat_1(sK1)
    | spl2_18 ),
    inference(avatar_component_clause,[],[f199])).

fof(f806,plain,
    ( spl2_59
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f788,f192,f179,f803])).

fof(f179,plain,
    ( spl2_14
  <=> sK1 = k2_zfmisc_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f788,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f787,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f787,plain,
    ( sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f181,f194])).

fof(f181,plain,
    ( sK1 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f768,plain,(
    spl2_58 ),
    inference(avatar_contradiction_clause,[],[f765])).

fof(f765,plain,
    ( $false
    | spl2_58 ),
    inference(unit_resulting_resolution,[],[f49,f763])).

fof(f763,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl2_58 ),
    inference(avatar_component_clause,[],[f761])).

fof(f761,plain,
    ( spl2_58
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f764,plain,
    ( ~ spl2_58
    | spl2_15
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f742,f192,f183,f761])).

fof(f183,plain,
    ( spl2_15
  <=> r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f742,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl2_15
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f722,f91])).

fof(f722,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1)
    | spl2_15
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f185,f194])).

fof(f185,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | spl2_15 ),
    inference(avatar_component_clause,[],[f183])).

fof(f711,plain,
    ( ~ spl2_9
    | ~ spl2_13
    | ~ spl2_46
    | ~ spl2_54 ),
    inference(avatar_contradiction_clause,[],[f709])).

fof(f709,plain,
    ( $false
    | ~ spl2_9
    | ~ spl2_13
    | ~ spl2_46
    | ~ spl2_54 ),
    inference(unit_resulting_resolution,[],[f154,f176,f609,f548])).

fof(f548,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0) )
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl2_46
  <=> ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f609,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl2_54
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f176,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl2_13
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f154,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl2_9
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f616,plain,(
    spl2_54 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | spl2_54 ),
    inference(unit_resulting_resolution,[],[f86,f610,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f610,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | spl2_54 ),
    inference(avatar_component_clause,[],[f608])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f50,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f611,plain,
    ( ~ spl2_5
    | ~ spl2_12
    | ~ spl2_1
    | ~ spl2_54
    | ~ spl2_18
    | spl2_53 ),
    inference(avatar_split_clause,[],[f606,f601,f199,f608,f101,f169,f133])).

fof(f133,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f169,plain,
    ( spl2_12
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f101,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f601,plain,
    ( spl2_53
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f606,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_18
    | spl2_53 ),
    inference(forward_demodulation,[],[f605,f201])).

fof(f201,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f199])).

fof(f605,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_53 ),
    inference(superposition,[],[f603,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f603,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_53 ),
    inference(avatar_component_clause,[],[f601])).

fof(f604,plain,
    ( ~ spl2_1
    | ~ spl2_28
    | ~ spl2_24
    | ~ spl2_4
    | ~ spl2_53
    | spl2_47 ),
    inference(avatar_split_clause,[],[f560,f556,f601,f116,f267,f288,f101])).

fof(f288,plain,
    ( spl2_28
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f267,plain,
    ( spl2_24
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f116,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f556,plain,
    ( spl2_47
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f560,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl2_47 ),
    inference(superposition,[],[f558,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f558,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_47 ),
    inference(avatar_component_clause,[],[f556])).

fof(f559,plain,
    ( ~ spl2_47
    | spl2_7
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f550,f257,f142,f556])).

fof(f142,plain,
    ( spl2_7
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f257,plain,
    ( spl2_23
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f550,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_7
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f144,f259])).

fof(f259,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f257])).

fof(f144,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f549,plain,
    ( ~ spl2_5
    | spl2_46
    | spl2_41 ),
    inference(avatar_split_clause,[],[f375,f371,f547,f133])).

fof(f371,plain,
    ( spl2_41
  <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v5_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1)
        | ~ v2_funct_2(sK1,X0) )
    | spl2_41 ),
    inference(superposition,[],[f373,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f373,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | spl2_41 ),
    inference(avatar_component_clause,[],[f371])).

fof(f374,plain,
    ( ~ spl2_5
    | ~ spl2_12
    | ~ spl2_1
    | ~ spl2_41
    | spl2_29 ),
    inference(avatar_split_clause,[],[f323,f292,f371,f101,f169,f133])).

fof(f292,plain,
    ( spl2_29
  <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f323,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_29 ),
    inference(superposition,[],[f294,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f294,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f292])).

fof(f302,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_3
    | ~ spl2_2
    | spl2_28
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f265,f257,f288,f106,f111,f116,f101])).

fof(f111,plain,
    ( spl2_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f106,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f265,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl2_23 ),
    inference(superposition,[],[f61,f259])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f295,plain,
    ( ~ spl2_24
    | ~ spl2_4
    | ~ spl2_1
    | ~ spl2_28
    | ~ spl2_29
    | spl2_25 ),
    inference(avatar_split_clause,[],[f276,f272,f292,f288,f101,f116,f267])).

fof(f272,plain,
    ( spl2_25
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f276,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl2_25 ),
    inference(superposition,[],[f274,f84])).

fof(f274,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f272])).

fof(f275,plain,
    ( ~ spl2_25
    | spl2_6
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f262,f257,f138,f272])).

fof(f138,plain,
    ( spl2_6
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f262,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_6
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f140,f259])).

fof(f140,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f270,plain,
    ( spl2_24
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f261,f257,f238,f267])).

fof(f238,plain,
    ( spl2_20
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f261,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_20
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f240,f259])).

fof(f240,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f238])).

fof(f260,plain,
    ( spl2_23
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f121,f116,f106,f111,f101,f257])).

fof(f121,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f118,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f118,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f241,plain,
    ( spl2_20
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f120,f116,f106,f111,f101,f238])).

fof(f120,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f118,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f202,plain,
    ( ~ spl2_4
    | spl2_18
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f196,f188,f199,f116])).

fof(f188,plain,
    ( spl2_16
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f196,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_16 ),
    inference(superposition,[],[f190,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f190,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f195,plain,
    ( ~ spl2_2
    | spl2_16
    | spl2_17
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f126,f116,f192,f188,f106])).

fof(f126,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f118,f79])).

fof(f79,plain,(
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

fof(f186,plain,
    ( spl2_14
    | ~ spl2_15
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f167,f162,f183,f179])).

fof(f162,plain,
    ( spl2_11
  <=> r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f167,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)
    | sK1 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_11 ),
    inference(resolution,[],[f164,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f164,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f177,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f128,f116,f101,f111,f174])).

fof(f128,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_2(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f118,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f172,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f127,f116,f101,f111,f169])).

fof(f127,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f118,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f165,plain,
    ( spl2_11
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f131,f116,f162])).

fof(f131,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f118,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f155,plain,
    ( spl2_9
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f124,f116,f152])).

fof(f124,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f118,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f145,plain,
    ( ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f85,f142,f138])).

fof(f85,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f42,f50,f50])).

fof(f42,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f136,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f122,f116,f133])).

fof(f122,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f118,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f119,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f46,f116])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f114,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f111])).

fof(f45,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f44,f106])).

fof(f44,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f43,f101])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (29076)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (29095)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (29089)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (29091)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (29075)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (29083)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (29073)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (29074)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (29077)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (29094)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (29081)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (29078)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (29072)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (29099)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (29087)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (29096)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (29101)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (29084)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.55  % (29088)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (29090)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (29079)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (29097)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (29093)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (29102)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (29082)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (29086)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.56  % (29088)Refutation not found, incomplete strategy% (29088)------------------------------
% 0.20/0.56  % (29088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (29088)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (29088)Memory used [KB]: 10746
% 0.20/0.56  % (29088)Time elapsed: 0.110 s
% 0.20/0.56  % (29088)------------------------------
% 0.20/0.56  % (29088)------------------------------
% 0.20/0.56  % (29085)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (29080)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.56  % (29098)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.54/0.56  % (29100)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.67/0.60  % (29101)Refutation found. Thanks to Tanya!
% 1.67/0.60  % SZS status Theorem for theBenchmark
% 1.67/0.61  % SZS output start Proof for theBenchmark
% 1.67/0.61  fof(f918,plain,(
% 1.67/0.61    $false),
% 1.67/0.61    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f136,f145,f155,f165,f172,f177,f186,f195,f202,f241,f260,f270,f275,f295,f302,f374,f549,f559,f604,f611,f616,f711,f764,f768,f806,f912,f917])).
% 1.67/0.61  fof(f917,plain,(
% 1.67/0.61    spl2_76),
% 1.67/0.61    inference(avatar_contradiction_clause,[],[f913])).
% 1.67/0.61  fof(f913,plain,(
% 1.67/0.61    $false | spl2_76),
% 1.67/0.61    inference(unit_resulting_resolution,[],[f47,f911])).
% 1.67/0.61  fof(f911,plain,(
% 1.67/0.61    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl2_76),
% 1.67/0.61    inference(avatar_component_clause,[],[f909])).
% 1.67/0.61  fof(f909,plain,(
% 1.67/0.61    spl2_76 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 1.67/0.61  fof(f47,plain,(
% 1.67/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.67/0.61    inference(cnf_transformation,[],[f5])).
% 1.67/0.61  fof(f5,axiom,(
% 1.67/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.67/0.61  fof(f912,plain,(
% 1.67/0.61    ~spl2_76 | ~spl2_17 | spl2_18 | ~spl2_59),
% 1.67/0.61    inference(avatar_split_clause,[],[f858,f803,f199,f192,f909])).
% 1.67/0.61  fof(f192,plain,(
% 1.67/0.61    spl2_17 <=> k1_xboole_0 = sK0),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.67/0.61  fof(f199,plain,(
% 1.67/0.61    spl2_18 <=> sK0 = k1_relat_1(sK1)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.67/0.61  fof(f803,plain,(
% 1.67/0.61    spl2_59 <=> k1_xboole_0 = sK1),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 1.67/0.61  fof(f858,plain,(
% 1.67/0.61    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl2_17 | spl2_18 | ~spl2_59)),
% 1.67/0.61    inference(forward_demodulation,[],[f759,f805])).
% 1.67/0.61  fof(f805,plain,(
% 1.67/0.61    k1_xboole_0 = sK1 | ~spl2_59),
% 1.67/0.61    inference(avatar_component_clause,[],[f803])).
% 1.67/0.61  fof(f759,plain,(
% 1.67/0.61    k1_xboole_0 != k1_relat_1(sK1) | (~spl2_17 | spl2_18)),
% 1.67/0.61    inference(forward_demodulation,[],[f200,f194])).
% 1.67/0.61  fof(f194,plain,(
% 1.67/0.61    k1_xboole_0 = sK0 | ~spl2_17),
% 1.67/0.61    inference(avatar_component_clause,[],[f192])).
% 1.67/0.61  fof(f200,plain,(
% 1.67/0.61    sK0 != k1_relat_1(sK1) | spl2_18),
% 1.67/0.61    inference(avatar_component_clause,[],[f199])).
% 1.67/0.61  fof(f806,plain,(
% 1.67/0.61    spl2_59 | ~spl2_14 | ~spl2_17),
% 1.67/0.61    inference(avatar_split_clause,[],[f788,f192,f179,f803])).
% 1.67/0.61  fof(f179,plain,(
% 1.67/0.61    spl2_14 <=> sK1 = k2_zfmisc_1(sK0,sK0)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.67/0.61  fof(f788,plain,(
% 1.67/0.61    k1_xboole_0 = sK1 | (~spl2_14 | ~spl2_17)),
% 1.67/0.61    inference(forward_demodulation,[],[f787,f91])).
% 1.67/0.61  fof(f91,plain,(
% 1.67/0.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.67/0.61    inference(equality_resolution,[],[f69])).
% 1.67/0.61  fof(f69,plain,(
% 1.67/0.61    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f3])).
% 1.67/0.61  fof(f3,axiom,(
% 1.67/0.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.67/0.61  fof(f787,plain,(
% 1.67/0.61    sK1 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) | (~spl2_14 | ~spl2_17)),
% 1.67/0.61    inference(forward_demodulation,[],[f181,f194])).
% 1.67/0.61  fof(f181,plain,(
% 1.67/0.61    sK1 = k2_zfmisc_1(sK0,sK0) | ~spl2_14),
% 1.67/0.61    inference(avatar_component_clause,[],[f179])).
% 1.67/0.61  fof(f768,plain,(
% 1.67/0.61    spl2_58),
% 1.67/0.61    inference(avatar_contradiction_clause,[],[f765])).
% 1.67/0.61  fof(f765,plain,(
% 1.67/0.61    $false | spl2_58),
% 1.67/0.61    inference(unit_resulting_resolution,[],[f49,f763])).
% 1.67/0.61  fof(f763,plain,(
% 1.67/0.61    ~r1_tarski(k1_xboole_0,sK1) | spl2_58),
% 1.67/0.61    inference(avatar_component_clause,[],[f761])).
% 1.67/0.61  fof(f761,plain,(
% 1.67/0.61    spl2_58 <=> r1_tarski(k1_xboole_0,sK1)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 1.67/0.61  fof(f49,plain,(
% 1.67/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f2])).
% 1.67/0.61  fof(f2,axiom,(
% 1.67/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.67/0.61  fof(f764,plain,(
% 1.67/0.61    ~spl2_58 | spl2_15 | ~spl2_17),
% 1.67/0.61    inference(avatar_split_clause,[],[f742,f192,f183,f761])).
% 1.67/0.61  fof(f183,plain,(
% 1.67/0.61    spl2_15 <=> r1_tarski(k2_zfmisc_1(sK0,sK0),sK1)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.67/0.61  fof(f742,plain,(
% 1.67/0.61    ~r1_tarski(k1_xboole_0,sK1) | (spl2_15 | ~spl2_17)),
% 1.67/0.61    inference(forward_demodulation,[],[f722,f91])).
% 1.67/0.61  fof(f722,plain,(
% 1.67/0.61    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) | (spl2_15 | ~spl2_17)),
% 1.67/0.61    inference(backward_demodulation,[],[f185,f194])).
% 1.67/0.61  fof(f185,plain,(
% 1.67/0.61    ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | spl2_15),
% 1.67/0.61    inference(avatar_component_clause,[],[f183])).
% 1.67/0.61  fof(f711,plain,(
% 1.67/0.61    ~spl2_9 | ~spl2_13 | ~spl2_46 | ~spl2_54),
% 1.67/0.61    inference(avatar_contradiction_clause,[],[f709])).
% 1.67/0.61  fof(f709,plain,(
% 1.67/0.61    $false | (~spl2_9 | ~spl2_13 | ~spl2_46 | ~spl2_54)),
% 1.67/0.61    inference(unit_resulting_resolution,[],[f154,f176,f609,f548])).
% 1.67/0.61  fof(f548,plain,(
% 1.67/0.61    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0)) ) | ~spl2_46),
% 1.67/0.61    inference(avatar_component_clause,[],[f547])).
% 1.67/0.61  fof(f547,plain,(
% 1.67/0.61    spl2_46 <=> ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 1.67/0.61  fof(f609,plain,(
% 1.67/0.61    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~spl2_54),
% 1.67/0.61    inference(avatar_component_clause,[],[f608])).
% 1.67/0.61  fof(f608,plain,(
% 1.67/0.61    spl2_54 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 1.67/0.61  fof(f176,plain,(
% 1.67/0.61    v2_funct_2(sK1,sK0) | ~spl2_13),
% 1.67/0.61    inference(avatar_component_clause,[],[f174])).
% 1.67/0.61  fof(f174,plain,(
% 1.67/0.61    spl2_13 <=> v2_funct_2(sK1,sK0)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.67/0.61  fof(f154,plain,(
% 1.67/0.61    v5_relat_1(sK1,sK0) | ~spl2_9),
% 1.67/0.61    inference(avatar_component_clause,[],[f152])).
% 1.67/0.61  fof(f152,plain,(
% 1.67/0.61    spl2_9 <=> v5_relat_1(sK1,sK0)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.67/0.61  fof(f616,plain,(
% 1.67/0.61    spl2_54),
% 1.67/0.61    inference(avatar_contradiction_clause,[],[f613])).
% 1.67/0.61  fof(f613,plain,(
% 1.67/0.61    $false | spl2_54),
% 1.67/0.61    inference(unit_resulting_resolution,[],[f86,f610,f99])).
% 1.67/0.61  fof(f99,plain,(
% 1.67/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.67/0.61    inference(duplicate_literal_removal,[],[f98])).
% 1.67/0.61  fof(f98,plain,(
% 1.67/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.67/0.61    inference(equality_resolution,[],[f82])).
% 1.67/0.61  fof(f82,plain,(
% 1.67/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f39])).
% 1.67/0.61  fof(f39,plain,(
% 1.67/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.61    inference(flattening,[],[f38])).
% 1.67/0.61  fof(f38,plain,(
% 1.67/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.67/0.61    inference(ennf_transformation,[],[f10])).
% 1.67/0.61  fof(f10,axiom,(
% 1.67/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.67/0.61  fof(f610,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | spl2_54),
% 1.67/0.61    inference(avatar_component_clause,[],[f608])).
% 1.67/0.61  fof(f86,plain,(
% 1.67/0.61    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.67/0.61    inference(definition_unfolding,[],[f52,f50])).
% 1.67/0.61  fof(f50,plain,(
% 1.67/0.61    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f18])).
% 1.67/0.61  fof(f18,axiom,(
% 1.67/0.61    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.67/0.61  fof(f52,plain,(
% 1.67/0.61    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.67/0.61    inference(cnf_transformation,[],[f15])).
% 1.67/0.61  fof(f15,axiom,(
% 1.67/0.61    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.67/0.61  fof(f611,plain,(
% 1.67/0.61    ~spl2_5 | ~spl2_12 | ~spl2_1 | ~spl2_54 | ~spl2_18 | spl2_53),
% 1.67/0.61    inference(avatar_split_clause,[],[f606,f601,f199,f608,f101,f169,f133])).
% 1.67/0.61  fof(f133,plain,(
% 1.67/0.61    spl2_5 <=> v1_relat_1(sK1)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.67/0.61  fof(f169,plain,(
% 1.67/0.61    spl2_12 <=> v2_funct_1(sK1)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.67/0.61  fof(f101,plain,(
% 1.67/0.61    spl2_1 <=> v1_funct_1(sK1)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.67/0.61  fof(f601,plain,(
% 1.67/0.61    spl2_53 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 1.67/0.61  fof(f606,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl2_18 | spl2_53)),
% 1.67/0.61    inference(forward_demodulation,[],[f605,f201])).
% 1.67/0.61  fof(f201,plain,(
% 1.67/0.61    sK0 = k1_relat_1(sK1) | ~spl2_18),
% 1.67/0.61    inference(avatar_component_clause,[],[f199])).
% 1.67/0.61  fof(f605,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_53),
% 1.67/0.61    inference(superposition,[],[f603,f53])).
% 1.67/0.61  fof(f53,plain,(
% 1.67/0.61    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f24])).
% 1.67/0.61  fof(f24,plain,(
% 1.67/0.61    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.67/0.61    inference(flattening,[],[f23])).
% 1.67/0.61  fof(f23,plain,(
% 1.67/0.61    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.67/0.61    inference(ennf_transformation,[],[f6])).
% 1.67/0.61  fof(f6,axiom,(
% 1.67/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.67/0.61  fof(f603,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_53),
% 1.67/0.61    inference(avatar_component_clause,[],[f601])).
% 1.67/0.61  fof(f604,plain,(
% 1.67/0.61    ~spl2_1 | ~spl2_28 | ~spl2_24 | ~spl2_4 | ~spl2_53 | spl2_47),
% 1.67/0.61    inference(avatar_split_clause,[],[f560,f556,f601,f116,f267,f288,f101])).
% 1.67/0.61  fof(f288,plain,(
% 1.67/0.61    spl2_28 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 1.67/0.61  fof(f267,plain,(
% 1.67/0.61    spl2_24 <=> v1_funct_1(k2_funct_1(sK1))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.67/0.61  fof(f116,plain,(
% 1.67/0.61    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.67/0.61  fof(f556,plain,(
% 1.67/0.61    spl2_47 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 1.67/0.61  fof(f560,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl2_47),
% 1.67/0.61    inference(superposition,[],[f558,f84])).
% 1.67/0.61  fof(f84,plain,(
% 1.67/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f41])).
% 1.67/0.61  fof(f41,plain,(
% 1.67/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.67/0.61    inference(flattening,[],[f40])).
% 1.67/0.61  fof(f40,plain,(
% 1.67/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.67/0.61    inference(ennf_transformation,[],[f16])).
% 1.67/0.61  fof(f16,axiom,(
% 1.67/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.67/0.61  fof(f558,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_47),
% 1.67/0.61    inference(avatar_component_clause,[],[f556])).
% 1.67/0.61  fof(f559,plain,(
% 1.67/0.61    ~spl2_47 | spl2_7 | ~spl2_23),
% 1.67/0.61    inference(avatar_split_clause,[],[f550,f257,f142,f556])).
% 1.67/0.61  fof(f142,plain,(
% 1.67/0.61    spl2_7 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.67/0.61  fof(f257,plain,(
% 1.67/0.61    spl2_23 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.67/0.61  fof(f550,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | (spl2_7 | ~spl2_23)),
% 1.67/0.61    inference(forward_demodulation,[],[f144,f259])).
% 1.67/0.61  fof(f259,plain,(
% 1.67/0.61    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl2_23),
% 1.67/0.61    inference(avatar_component_clause,[],[f257])).
% 1.67/0.61  fof(f144,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl2_7),
% 1.67/0.61    inference(avatar_component_clause,[],[f142])).
% 1.67/0.61  fof(f549,plain,(
% 1.67/0.61    ~spl2_5 | spl2_46 | spl2_41),
% 1.67/0.61    inference(avatar_split_clause,[],[f375,f371,f547,f133])).
% 1.67/0.61  fof(f371,plain,(
% 1.67/0.61    spl2_41 <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 1.67/0.61  fof(f375,plain,(
% 1.67/0.61    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1) | ~v2_funct_2(sK1,X0)) ) | spl2_41),
% 1.67/0.61    inference(superposition,[],[f373,f56])).
% 1.67/0.61  fof(f56,plain,(
% 1.67/0.61    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v2_funct_2(X1,X0)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f26])).
% 1.67/0.61  fof(f26,plain,(
% 1.67/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.67/0.61    inference(flattening,[],[f25])).
% 1.67/0.61  fof(f25,plain,(
% 1.67/0.61    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.67/0.61    inference(ennf_transformation,[],[f13])).
% 1.67/0.61  fof(f13,axiom,(
% 1.67/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.67/0.61  fof(f373,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | spl2_41),
% 1.67/0.61    inference(avatar_component_clause,[],[f371])).
% 1.67/0.61  fof(f374,plain,(
% 1.67/0.61    ~spl2_5 | ~spl2_12 | ~spl2_1 | ~spl2_41 | spl2_29),
% 1.67/0.61    inference(avatar_split_clause,[],[f323,f292,f371,f101,f169,f133])).
% 1.67/0.61  fof(f292,plain,(
% 1.67/0.61    spl2_29 <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 1.67/0.61  fof(f323,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_29),
% 1.67/0.61    inference(superposition,[],[f294,f54])).
% 1.67/0.61  fof(f54,plain,(
% 1.67/0.61    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f24])).
% 1.67/0.61  fof(f294,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_29),
% 1.67/0.61    inference(avatar_component_clause,[],[f292])).
% 1.67/0.61  fof(f302,plain,(
% 1.67/0.61    ~spl2_1 | ~spl2_4 | ~spl2_3 | ~spl2_2 | spl2_28 | ~spl2_23),
% 1.67/0.61    inference(avatar_split_clause,[],[f265,f257,f288,f106,f111,f116,f101])).
% 1.67/0.61  fof(f111,plain,(
% 1.67/0.61    spl2_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.67/0.61  fof(f106,plain,(
% 1.67/0.61    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.67/0.61  fof(f265,plain,(
% 1.67/0.61    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl2_23),
% 1.67/0.61    inference(superposition,[],[f61,f259])).
% 1.67/0.61  fof(f61,plain,(
% 1.67/0.61    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f30])).
% 1.67/0.61  fof(f30,plain,(
% 1.67/0.61    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.67/0.61    inference(flattening,[],[f29])).
% 1.67/0.61  fof(f29,plain,(
% 1.67/0.61    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.67/0.61    inference(ennf_transformation,[],[f14])).
% 1.67/0.61  fof(f14,axiom,(
% 1.67/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.67/0.61  fof(f295,plain,(
% 1.67/0.61    ~spl2_24 | ~spl2_4 | ~spl2_1 | ~spl2_28 | ~spl2_29 | spl2_25),
% 1.67/0.61    inference(avatar_split_clause,[],[f276,f272,f292,f288,f101,f116,f267])).
% 1.67/0.61  fof(f272,plain,(
% 1.67/0.61    spl2_25 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 1.67/0.61  fof(f276,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | spl2_25),
% 1.67/0.61    inference(superposition,[],[f274,f84])).
% 1.67/0.61  fof(f274,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_25),
% 1.67/0.61    inference(avatar_component_clause,[],[f272])).
% 1.67/0.61  fof(f275,plain,(
% 1.67/0.61    ~spl2_25 | spl2_6 | ~spl2_23),
% 1.67/0.61    inference(avatar_split_clause,[],[f262,f257,f138,f272])).
% 1.67/0.61  fof(f138,plain,(
% 1.67/0.61    spl2_6 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.67/0.61  fof(f262,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | (spl2_6 | ~spl2_23)),
% 1.67/0.61    inference(backward_demodulation,[],[f140,f259])).
% 1.67/0.61  fof(f140,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl2_6),
% 1.67/0.61    inference(avatar_component_clause,[],[f138])).
% 1.67/0.61  fof(f270,plain,(
% 1.67/0.61    spl2_24 | ~spl2_20 | ~spl2_23),
% 1.67/0.61    inference(avatar_split_clause,[],[f261,f257,f238,f267])).
% 1.67/0.61  fof(f238,plain,(
% 1.67/0.61    spl2_20 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.67/0.61  fof(f261,plain,(
% 1.67/0.61    v1_funct_1(k2_funct_1(sK1)) | (~spl2_20 | ~spl2_23)),
% 1.67/0.61    inference(backward_demodulation,[],[f240,f259])).
% 1.67/0.61  fof(f240,plain,(
% 1.67/0.61    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl2_20),
% 1.67/0.61    inference(avatar_component_clause,[],[f238])).
% 1.67/0.61  fof(f260,plain,(
% 1.67/0.61    spl2_23 | ~spl2_1 | ~spl2_3 | ~spl2_2 | ~spl2_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f121,f116,f106,f111,f101,f257])).
% 1.67/0.61  fof(f121,plain,(
% 1.67/0.61    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl2_4),
% 1.67/0.61    inference(resolution,[],[f118,f57])).
% 1.67/0.61  fof(f57,plain,(
% 1.67/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f28])).
% 1.67/0.61  fof(f28,plain,(
% 1.67/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.67/0.61    inference(flattening,[],[f27])).
% 1.67/0.61  fof(f27,plain,(
% 1.67/0.61    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.67/0.61    inference(ennf_transformation,[],[f17])).
% 1.67/0.61  fof(f17,axiom,(
% 1.67/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.67/0.61  fof(f118,plain,(
% 1.67/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_4),
% 1.67/0.61    inference(avatar_component_clause,[],[f116])).
% 1.67/0.61  fof(f241,plain,(
% 1.67/0.61    spl2_20 | ~spl2_1 | ~spl2_3 | ~spl2_2 | ~spl2_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f120,f116,f106,f111,f101,f238])).
% 1.67/0.61  fof(f120,plain,(
% 1.67/0.61    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl2_4),
% 1.67/0.61    inference(resolution,[],[f118,f58])).
% 1.67/0.61  fof(f58,plain,(
% 1.67/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 1.67/0.61    inference(cnf_transformation,[],[f30])).
% 1.67/0.61  fof(f202,plain,(
% 1.67/0.61    ~spl2_4 | spl2_18 | ~spl2_16),
% 1.67/0.61    inference(avatar_split_clause,[],[f196,f188,f199,f116])).
% 1.67/0.61  fof(f188,plain,(
% 1.67/0.61    spl2_16 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.67/0.61  fof(f196,plain,(
% 1.67/0.61    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_16),
% 1.67/0.61    inference(superposition,[],[f190,f71])).
% 1.67/0.61  fof(f71,plain,(
% 1.67/0.61    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.61    inference(cnf_transformation,[],[f32])).
% 1.67/0.61  fof(f32,plain,(
% 1.67/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.61    inference(ennf_transformation,[],[f9])).
% 1.67/0.61  fof(f9,axiom,(
% 1.67/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.67/0.61  fof(f190,plain,(
% 1.67/0.61    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_16),
% 1.67/0.61    inference(avatar_component_clause,[],[f188])).
% 1.67/0.61  fof(f195,plain,(
% 1.67/0.61    ~spl2_2 | spl2_16 | spl2_17 | ~spl2_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f126,f116,f192,f188,f106])).
% 1.67/0.61  fof(f126,plain,(
% 1.67/0.61    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~spl2_4),
% 1.67/0.61    inference(resolution,[],[f118,f79])).
% 1.67/0.61  fof(f79,plain,(
% 1.67/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f35])).
% 1.67/0.61  fof(f35,plain,(
% 1.67/0.61    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.61    inference(flattening,[],[f34])).
% 1.67/0.61  fof(f34,plain,(
% 1.67/0.61    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.61    inference(ennf_transformation,[],[f12])).
% 1.67/0.61  fof(f12,axiom,(
% 1.67/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.67/0.61  fof(f186,plain,(
% 1.67/0.61    spl2_14 | ~spl2_15 | ~spl2_11),
% 1.67/0.61    inference(avatar_split_clause,[],[f167,f162,f183,f179])).
% 1.67/0.61  fof(f162,plain,(
% 1.67/0.61    spl2_11 <=> r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 1.67/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.67/0.61  fof(f167,plain,(
% 1.67/0.61    ~r1_tarski(k2_zfmisc_1(sK0,sK0),sK1) | sK1 = k2_zfmisc_1(sK0,sK0) | ~spl2_11),
% 1.67/0.61    inference(resolution,[],[f164,f64])).
% 1.67/0.61  fof(f64,plain,(
% 1.67/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.67/0.61    inference(cnf_transformation,[],[f1])).
% 1.67/0.61  fof(f1,axiom,(
% 1.67/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.67/0.61  fof(f164,plain,(
% 1.67/0.61    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) | ~spl2_11),
% 1.67/0.61    inference(avatar_component_clause,[],[f162])).
% 1.67/0.61  fof(f177,plain,(
% 1.67/0.61    spl2_13 | ~spl2_3 | ~spl2_1 | ~spl2_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f128,f116,f101,f111,f174])).
% 1.67/0.61  fof(f128,plain,(
% 1.67/0.61    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_2(sK1,sK0) | ~spl2_4),
% 1.67/0.61    inference(resolution,[],[f118,f81])).
% 1.67/0.61  fof(f81,plain,(
% 1.67/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f37])).
% 1.67/0.61  fof(f37,plain,(
% 1.67/0.61    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.61    inference(flattening,[],[f36])).
% 1.67/0.61  fof(f36,plain,(
% 1.67/0.61    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.61    inference(ennf_transformation,[],[f11])).
% 1.67/0.61  fof(f11,axiom,(
% 1.67/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.67/0.61  fof(f172,plain,(
% 1.67/0.61    spl2_12 | ~spl2_3 | ~spl2_1 | ~spl2_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f127,f116,f101,f111,f169])).
% 1.67/0.61  fof(f127,plain,(
% 1.67/0.61    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_1(sK1) | ~spl2_4),
% 1.67/0.61    inference(resolution,[],[f118,f80])).
% 1.67/0.61  fof(f80,plain,(
% 1.67/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f37])).
% 1.67/0.61  fof(f165,plain,(
% 1.67/0.61    spl2_11 | ~spl2_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f131,f116,f162])).
% 1.67/0.61  fof(f131,plain,(
% 1.67/0.61    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) | ~spl2_4),
% 1.67/0.61    inference(resolution,[],[f118,f66])).
% 1.67/0.61  fof(f66,plain,(
% 1.67/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f4])).
% 1.67/0.61  fof(f4,axiom,(
% 1.67/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.67/0.61  fof(f155,plain,(
% 1.67/0.61    spl2_9 | ~spl2_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f124,f116,f152])).
% 1.67/0.61  fof(f124,plain,(
% 1.67/0.61    v5_relat_1(sK1,sK0) | ~spl2_4),
% 1.67/0.61    inference(resolution,[],[f118,f73])).
% 1.67/0.61  fof(f73,plain,(
% 1.67/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f33])).
% 1.67/0.61  fof(f33,plain,(
% 1.67/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.61    inference(ennf_transformation,[],[f8])).
% 1.67/0.61  fof(f8,axiom,(
% 1.67/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.67/0.61  fof(f145,plain,(
% 1.67/0.61    ~spl2_6 | ~spl2_7),
% 1.67/0.61    inference(avatar_split_clause,[],[f85,f142,f138])).
% 1.67/0.61  fof(f85,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 1.67/0.61    inference(definition_unfolding,[],[f42,f50,f50])).
% 1.67/0.61  fof(f42,plain,(
% 1.67/0.61    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 1.67/0.61    inference(cnf_transformation,[],[f22])).
% 1.67/0.61  fof(f22,plain,(
% 1.67/0.61    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.67/0.61    inference(flattening,[],[f21])).
% 1.67/0.61  fof(f21,plain,(
% 1.67/0.61    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.67/0.61    inference(ennf_transformation,[],[f20])).
% 1.67/0.61  fof(f20,negated_conjecture,(
% 1.67/0.61    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.67/0.61    inference(negated_conjecture,[],[f19])).
% 1.67/0.61  fof(f19,conjecture,(
% 1.67/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 1.67/0.61  fof(f136,plain,(
% 1.67/0.61    spl2_5 | ~spl2_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f122,f116,f133])).
% 1.67/0.61  fof(f122,plain,(
% 1.67/0.61    v1_relat_1(sK1) | ~spl2_4),
% 1.67/0.61    inference(resolution,[],[f118,f70])).
% 1.67/0.61  fof(f70,plain,(
% 1.67/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.67/0.61    inference(cnf_transformation,[],[f31])).
% 1.67/0.61  fof(f31,plain,(
% 1.67/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.61    inference(ennf_transformation,[],[f7])).
% 1.67/0.61  fof(f7,axiom,(
% 1.67/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.67/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.67/0.61  fof(f119,plain,(
% 1.67/0.61    spl2_4),
% 1.67/0.61    inference(avatar_split_clause,[],[f46,f116])).
% 1.67/0.61  fof(f46,plain,(
% 1.67/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.67/0.61    inference(cnf_transformation,[],[f22])).
% 1.67/0.61  fof(f114,plain,(
% 1.67/0.61    spl2_3),
% 1.67/0.61    inference(avatar_split_clause,[],[f45,f111])).
% 1.67/0.61  fof(f45,plain,(
% 1.67/0.61    v3_funct_2(sK1,sK0,sK0)),
% 1.67/0.61    inference(cnf_transformation,[],[f22])).
% 1.67/0.61  fof(f109,plain,(
% 1.67/0.61    spl2_2),
% 1.67/0.61    inference(avatar_split_clause,[],[f44,f106])).
% 1.67/0.61  fof(f44,plain,(
% 1.67/0.61    v1_funct_2(sK1,sK0,sK0)),
% 1.67/0.61    inference(cnf_transformation,[],[f22])).
% 1.67/0.61  fof(f104,plain,(
% 1.67/0.61    spl2_1),
% 1.67/0.61    inference(avatar_split_clause,[],[f43,f101])).
% 1.67/0.61  fof(f43,plain,(
% 1.67/0.61    v1_funct_1(sK1)),
% 1.67/0.61    inference(cnf_transformation,[],[f22])).
% 1.67/0.61  % SZS output end Proof for theBenchmark
% 1.67/0.61  % (29101)------------------------------
% 1.67/0.61  % (29101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.61  % (29101)Termination reason: Refutation
% 1.67/0.61  
% 1.67/0.61  % (29101)Memory used [KB]: 11257
% 1.67/0.61  % (29101)Time elapsed: 0.179 s
% 1.67/0.61  % (29101)------------------------------
% 1.67/0.61  % (29101)------------------------------
% 1.67/0.61  % (29069)Success in time 0.255 s
%------------------------------------------------------------------------------
