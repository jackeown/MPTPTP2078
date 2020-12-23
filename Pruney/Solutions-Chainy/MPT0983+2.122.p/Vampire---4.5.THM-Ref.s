%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:52 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 342 expanded)
%              Number of leaves         :   49 ( 140 expanded)
%              Depth                    :   13
%              Number of atoms          :  703 (1413 expanded)
%              Number of equality atoms :   89 ( 106 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f865,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f159,f170,f218,f224,f246,f269,f576,f617,f641,f671,f701,f745,f807,f809,f820,f864])).

fof(f864,plain,
    ( spl4_1
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f863])).

fof(f863,plain,
    ( $false
    | spl4_1
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f860,f102])).

fof(f102,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f860,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(resolution,[],[f245,f173])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v2_funct_1(X0) )
    | ~ spl4_12 ),
    inference(superposition,[],[f158,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f158,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl4_12
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f245,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl4_23
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f820,plain,
    ( ~ spl4_31
    | spl4_22 ),
    inference(avatar_split_clause,[],[f459,f239,f388])).

fof(f388,plain,
    ( spl4_31
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f239,plain,
    ( spl4_22
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f459,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_22 ),
    inference(duplicate_literal_removal,[],[f453])).

fof(f453,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK0)
    | spl4_22 ),
    inference(superposition,[],[f241,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f95,f82])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f241,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f239])).

fof(f809,plain,
    ( spl4_2
    | ~ spl4_18
    | ~ spl4_24
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f808,f698,f266,f215,f104])).

fof(f104,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f215,plain,
    ( spl4_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f266,plain,
    ( spl4_24
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f698,plain,
    ( spl4_45
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f808,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ spl4_18
    | ~ spl4_24
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f800,f217])).

fof(f217,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f215])).

fof(f800,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_24
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f790,f268])).

fof(f268,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f266])).

fof(f790,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_45 ),
    inference(superposition,[],[f91,f700])).

fof(f700,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f698])).

fof(f91,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f807,plain,
    ( k1_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f745,plain,
    ( ~ spl4_18
    | ~ spl4_24
    | spl4_44 ),
    inference(avatar_contradiction_clause,[],[f744])).

fof(f744,plain,
    ( $false
    | ~ spl4_18
    | ~ spl4_24
    | spl4_44 ),
    inference(subsumption_resolution,[],[f743,f217])).

fof(f743,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_24
    | spl4_44 ),
    inference(subsumption_resolution,[],[f740,f268])).

fof(f740,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl4_44 ),
    inference(resolution,[],[f696,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f696,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl4_44 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl4_44
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f701,plain,
    ( ~ spl4_44
    | spl4_45
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f692,f582,f221,f215,f698,f694])).

fof(f221,plain,
    ( spl4_19
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f582,plain,
    ( spl4_41
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f692,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f691,f88])).

fof(f88,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f691,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0))
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f690,f88])).

fof(f690,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_relat_1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0))
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f689,f217])).

fof(f689,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_relat_1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_19
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f685,f223])).

fof(f223,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f221])).

fof(f685,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_relat_1(sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_41 ),
    inference(superposition,[],[f291,f584])).

fof(f584,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f582])).

fof(f291,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f86,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f671,plain,
    ( spl4_1
    | spl4_43
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f670,f573,f139,f134,f129,f124,f119,f114,f660,f100])).

fof(f660,plain,
    ( spl4_43
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f114,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f119,plain,
    ( spl4_5
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f124,plain,
    ( spl4_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f129,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f134,plain,
    ( spl4_8
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f139,plain,
    ( spl4_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f573,plain,
    ( spl4_39
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f670,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f669,f141])).

fof(f141,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f669,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f668,f136])).

fof(f136,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f668,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f667,f131])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f667,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f666,f126])).

fof(f126,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f666,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f665,f121])).

fof(f121,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f665,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f651,f116])).

fof(f116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f651,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f631,f65])).

fof(f65,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f631,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_39 ),
    inference(superposition,[],[f62,f575])).

fof(f575,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f573])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f641,plain,
    ( spl4_41
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f640,f573,f139,f129,f124,f114,f582])).

fof(f640,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f639,f141])).

fof(f639,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f638,f131])).

fof(f638,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f637,f126])).

fof(f637,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f629,f116])).

fof(f629,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_39 ),
    inference(superposition,[],[f71,f575])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f617,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | spl4_38 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | spl4_38 ),
    inference(subsumption_resolution,[],[f615,f141])).

fof(f615,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | spl4_38 ),
    inference(subsumption_resolution,[],[f614,f131])).

fof(f614,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | spl4_38 ),
    inference(subsumption_resolution,[],[f613,f126])).

fof(f613,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | spl4_38 ),
    inference(subsumption_resolution,[],[f608,f116])).

fof(f608,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_38 ),
    inference(resolution,[],[f571,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f571,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl4_38
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f576,plain,
    ( ~ spl4_38
    | spl4_39
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f564,f167,f573,f569])).

fof(f167,plain,
    ( spl4_14
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f564,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_14 ),
    inference(resolution,[],[f332,f169])).

fof(f169,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f332,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f66,f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f269,plain,
    ( spl4_24
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f260,f114,f266])).

fof(f260,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f89,f116])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f246,plain,
    ( ~ spl4_22
    | spl4_23
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f226,f129,f243,f239])).

fof(f226,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f73,f131])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f224,plain,
    ( spl4_19
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f219,f129,f221])).

fof(f219,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f210,f78])).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f210,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f72,f131])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f218,plain,
    ( spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f213,f114,f215])).

fof(f213,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f209,f78])).

fof(f209,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f72,f116])).

fof(f170,plain,
    ( spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f165,f109,f167])).

fof(f109,plain,
    ( spl4_3
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f165,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f111,f68])).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f111,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f159,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f153,f144,f156])).

fof(f144,plain,
    ( spl4_10
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f153,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_10 ),
    inference(superposition,[],[f65,f146])).

fof(f146,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f152,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f90,f149])).

fof(f149,plain,
    ( spl4_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f90,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f147,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f83,f144])).

fof(f83,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f142,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f52,f139])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f137,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f53,f134])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f132,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f54,f129])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f127,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f55,f124])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f122,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f56,f119])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f117,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f57,f114])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f112,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f58,f109])).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f107,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f59,f104,f100])).

fof(f59,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n024.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 15:13:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (3575)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.52  % (3592)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.52  % (3568)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.53  % (3591)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.53  % (3583)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.53  % (3576)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.53  % (3570)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.54  % (3569)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.54  % (3588)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.54  % (3580)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.55  % (3572)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.55  % (3573)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.55  % (3590)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.55  % (3582)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.55  % (3594)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.55  % (3593)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.23/0.55  % (3596)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.56  % (3584)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.56  % (3596)Refutation not found, incomplete strategy% (3596)------------------------------
% 0.23/0.56  % (3596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (3596)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (3596)Memory used [KB]: 10874
% 0.23/0.56  % (3596)Time elapsed: 0.132 s
% 0.23/0.56  % (3596)------------------------------
% 0.23/0.56  % (3596)------------------------------
% 0.23/0.56  % (3597)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.56  % (3571)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.56  % (3584)Refutation not found, incomplete strategy% (3584)------------------------------
% 0.23/0.56  % (3584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (3584)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (3584)Memory used [KB]: 10746
% 0.23/0.56  % (3584)Time elapsed: 0.101 s
% 0.23/0.56  % (3584)------------------------------
% 0.23/0.56  % (3584)------------------------------
% 0.23/0.56  % (3574)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.56  % (3585)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.56  % (3589)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.47/0.56  % (3586)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.47/0.57  % (3587)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.47/0.57  % (3578)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.47/0.57  % (3577)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.47/0.57  % (3581)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.47/0.57  % (3595)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.47/0.57  % (3579)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.47/0.58  % (3578)Refutation not found, incomplete strategy% (3578)------------------------------
% 1.47/0.58  % (3578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (3578)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (3578)Memory used [KB]: 10874
% 1.47/0.58  % (3578)Time elapsed: 0.151 s
% 1.47/0.58  % (3578)------------------------------
% 1.47/0.58  % (3578)------------------------------
% 1.71/0.60  % (3589)Refutation found. Thanks to Tanya!
% 1.71/0.60  % SZS status Theorem for theBenchmark
% 1.71/0.60  % SZS output start Proof for theBenchmark
% 1.71/0.60  fof(f865,plain,(
% 1.71/0.60    $false),
% 1.71/0.60    inference(avatar_sat_refutation,[],[f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f159,f170,f218,f224,f246,f269,f576,f617,f641,f671,f701,f745,f807,f809,f820,f864])).
% 1.71/0.60  fof(f864,plain,(
% 1.71/0.60    spl4_1 | ~spl4_12 | ~spl4_23),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f863])).
% 1.71/0.60  fof(f863,plain,(
% 1.71/0.60    $false | (spl4_1 | ~spl4_12 | ~spl4_23)),
% 1.71/0.60    inference(subsumption_resolution,[],[f860,f102])).
% 1.71/0.60  fof(f102,plain,(
% 1.71/0.60    ~v2_funct_1(sK2) | spl4_1),
% 1.71/0.60    inference(avatar_component_clause,[],[f100])).
% 1.71/0.60  fof(f100,plain,(
% 1.71/0.60    spl4_1 <=> v2_funct_1(sK2)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.71/0.60  fof(f860,plain,(
% 1.71/0.60    v2_funct_1(sK2) | (~spl4_12 | ~spl4_23)),
% 1.71/0.60    inference(resolution,[],[f245,f173])).
% 1.71/0.60  fof(f173,plain,(
% 1.71/0.60    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) ) | ~spl4_12),
% 1.71/0.60    inference(superposition,[],[f158,f82])).
% 1.71/0.60  fof(f82,plain,(
% 1.71/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f38])).
% 1.71/0.60  fof(f38,plain,(
% 1.71/0.60    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.71/0.60    inference(ennf_transformation,[],[f2])).
% 1.71/0.60  fof(f2,axiom,(
% 1.71/0.60    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.71/0.60  fof(f158,plain,(
% 1.71/0.60    v2_funct_1(k1_xboole_0) | ~spl4_12),
% 1.71/0.60    inference(avatar_component_clause,[],[f156])).
% 1.71/0.60  fof(f156,plain,(
% 1.71/0.60    spl4_12 <=> v2_funct_1(k1_xboole_0)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.71/0.60  fof(f245,plain,(
% 1.71/0.60    v1_xboole_0(sK2) | ~spl4_23),
% 1.71/0.60    inference(avatar_component_clause,[],[f243])).
% 1.71/0.60  fof(f243,plain,(
% 1.71/0.60    spl4_23 <=> v1_xboole_0(sK2)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.71/0.60  fof(f820,plain,(
% 1.71/0.60    ~spl4_31 | spl4_22),
% 1.71/0.60    inference(avatar_split_clause,[],[f459,f239,f388])).
% 1.71/0.60  fof(f388,plain,(
% 1.71/0.60    spl4_31 <=> v1_xboole_0(sK0)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.71/0.60  fof(f239,plain,(
% 1.71/0.60    spl4_22 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.71/0.60  fof(f459,plain,(
% 1.71/0.60    ~v1_xboole_0(sK0) | spl4_22),
% 1.71/0.60    inference(duplicate_literal_removal,[],[f453])).
% 1.71/0.60  fof(f453,plain,(
% 1.71/0.60    ~v1_xboole_0(sK0) | ~v1_xboole_0(sK0) | spl4_22),
% 1.71/0.60    inference(superposition,[],[f241,f192])).
% 1.71/0.60  fof(f192,plain,(
% 1.71/0.60    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 1.71/0.60    inference(superposition,[],[f95,f82])).
% 1.71/0.60  fof(f95,plain,(
% 1.71/0.60    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.71/0.60    inference(equality_resolution,[],[f76])).
% 1.71/0.60  fof(f76,plain,(
% 1.71/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.71/0.60    inference(cnf_transformation,[],[f48])).
% 1.71/0.60  fof(f48,plain,(
% 1.71/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.60    inference(flattening,[],[f47])).
% 1.71/0.60  fof(f47,plain,(
% 1.71/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.60    inference(nnf_transformation,[],[f4])).
% 1.71/0.60  fof(f4,axiom,(
% 1.71/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.71/0.60  fof(f241,plain,(
% 1.71/0.60    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_22),
% 1.71/0.60    inference(avatar_component_clause,[],[f239])).
% 1.71/0.60  fof(f809,plain,(
% 1.71/0.60    spl4_2 | ~spl4_18 | ~spl4_24 | ~spl4_45),
% 1.71/0.60    inference(avatar_split_clause,[],[f808,f698,f266,f215,f104])).
% 1.71/0.60  fof(f104,plain,(
% 1.71/0.60    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.71/0.60  fof(f215,plain,(
% 1.71/0.60    spl4_18 <=> v1_relat_1(sK3)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.71/0.60  fof(f266,plain,(
% 1.71/0.60    spl4_24 <=> v5_relat_1(sK3,sK0)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.71/0.60  fof(f698,plain,(
% 1.71/0.60    spl4_45 <=> sK0 = k2_relat_1(sK3)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.71/0.60  fof(f808,plain,(
% 1.71/0.60    v2_funct_2(sK3,sK0) | (~spl4_18 | ~spl4_24 | ~spl4_45)),
% 1.71/0.60    inference(subsumption_resolution,[],[f800,f217])).
% 1.71/0.60  fof(f217,plain,(
% 1.71/0.60    v1_relat_1(sK3) | ~spl4_18),
% 1.71/0.60    inference(avatar_component_clause,[],[f215])).
% 1.71/0.60  fof(f800,plain,(
% 1.71/0.60    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | (~spl4_24 | ~spl4_45)),
% 1.71/0.60    inference(subsumption_resolution,[],[f790,f268])).
% 1.71/0.60  fof(f268,plain,(
% 1.71/0.60    v5_relat_1(sK3,sK0) | ~spl4_24),
% 1.71/0.60    inference(avatar_component_clause,[],[f266])).
% 1.71/0.60  fof(f790,plain,(
% 1.71/0.60    ~v5_relat_1(sK3,sK0) | v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_45),
% 1.71/0.60    inference(superposition,[],[f91,f700])).
% 1.71/0.60  fof(f700,plain,(
% 1.71/0.60    sK0 = k2_relat_1(sK3) | ~spl4_45),
% 1.71/0.60    inference(avatar_component_clause,[],[f698])).
% 1.71/0.60  fof(f91,plain,(
% 1.71/0.60    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.71/0.60    inference(equality_resolution,[],[f61])).
% 1.71/0.60  fof(f61,plain,(
% 1.71/0.60    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f45])).
% 1.71/0.60  fof(f45,plain,(
% 1.71/0.60    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(nnf_transformation,[],[f27])).
% 1.71/0.60  fof(f27,plain,(
% 1.71/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(flattening,[],[f26])).
% 1.71/0.60  fof(f26,plain,(
% 1.71/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.71/0.60    inference(ennf_transformation,[],[f16])).
% 1.71/0.60  fof(f16,axiom,(
% 1.71/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.71/0.60  fof(f807,plain,(
% 1.71/0.60    k1_xboole_0 != sK0 | v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 1.71/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.71/0.60  fof(f745,plain,(
% 1.71/0.60    ~spl4_18 | ~spl4_24 | spl4_44),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f744])).
% 1.71/0.60  fof(f744,plain,(
% 1.71/0.60    $false | (~spl4_18 | ~spl4_24 | spl4_44)),
% 1.71/0.60    inference(subsumption_resolution,[],[f743,f217])).
% 1.71/0.60  fof(f743,plain,(
% 1.71/0.60    ~v1_relat_1(sK3) | (~spl4_24 | spl4_44)),
% 1.71/0.60    inference(subsumption_resolution,[],[f740,f268])).
% 1.71/0.60  fof(f740,plain,(
% 1.71/0.60    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl4_44),
% 1.71/0.60    inference(resolution,[],[f696,f84])).
% 1.71/0.60  fof(f84,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f51])).
% 1.71/0.60  fof(f51,plain,(
% 1.71/0.60    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(nnf_transformation,[],[f39])).
% 1.71/0.60  fof(f39,plain,(
% 1.71/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.71/0.60    inference(ennf_transformation,[],[f7])).
% 1.71/0.60  fof(f7,axiom,(
% 1.71/0.60    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.71/0.60  fof(f696,plain,(
% 1.71/0.60    ~r1_tarski(k2_relat_1(sK3),sK0) | spl4_44),
% 1.71/0.60    inference(avatar_component_clause,[],[f694])).
% 1.71/0.60  fof(f694,plain,(
% 1.71/0.60    spl4_44 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.71/0.60  fof(f701,plain,(
% 1.71/0.60    ~spl4_44 | spl4_45 | ~spl4_18 | ~spl4_19 | ~spl4_41),
% 1.71/0.60    inference(avatar_split_clause,[],[f692,f582,f221,f215,f698,f694])).
% 1.71/0.60  fof(f221,plain,(
% 1.71/0.60    spl4_19 <=> v1_relat_1(sK2)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.71/0.60  fof(f582,plain,(
% 1.71/0.60    spl4_41 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.71/0.60  fof(f692,plain,(
% 1.71/0.60    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0) | (~spl4_18 | ~spl4_19 | ~spl4_41)),
% 1.71/0.60    inference(forward_demodulation,[],[f691,f88])).
% 1.71/0.60  fof(f88,plain,(
% 1.71/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.71/0.60    inference(cnf_transformation,[],[f10])).
% 1.71/0.60  fof(f10,axiom,(
% 1.71/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.71/0.60  fof(f691,plain,(
% 1.71/0.60    ~r1_tarski(k2_relat_1(sK3),sK0) | k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0)) | (~spl4_18 | ~spl4_19 | ~spl4_41)),
% 1.71/0.60    inference(forward_demodulation,[],[f690,f88])).
% 1.71/0.60  fof(f690,plain,(
% 1.71/0.60    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_relat_1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0)) | (~spl4_18 | ~spl4_19 | ~spl4_41)),
% 1.71/0.60    inference(subsumption_resolution,[],[f689,f217])).
% 1.71/0.60  fof(f689,plain,(
% 1.71/0.60    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_relat_1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK3) | (~spl4_19 | ~spl4_41)),
% 1.71/0.60    inference(subsumption_resolution,[],[f685,f223])).
% 1.71/0.60  fof(f223,plain,(
% 1.71/0.60    v1_relat_1(sK2) | ~spl4_19),
% 1.71/0.60    inference(avatar_component_clause,[],[f221])).
% 1.71/0.60  fof(f685,plain,(
% 1.71/0.60    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_relat_1(sK0))) | ~v1_relat_1(sK2) | k2_relat_1(sK3) = k2_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(sK3) | ~spl4_41),
% 1.71/0.60    inference(superposition,[],[f291,f584])).
% 1.71/0.60  fof(f584,plain,(
% 1.71/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_41),
% 1.71/0.60    inference(avatar_component_clause,[],[f582])).
% 1.71/0.60  fof(f291,plain,(
% 1.71/0.60    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.71/0.60    inference(resolution,[],[f86,f81])).
% 1.71/0.60  fof(f81,plain,(
% 1.71/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f50])).
% 1.71/0.60  fof(f50,plain,(
% 1.71/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.60    inference(flattening,[],[f49])).
% 1.71/0.60  fof(f49,plain,(
% 1.71/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.60    inference(nnf_transformation,[],[f3])).
% 1.71/0.60  fof(f3,axiom,(
% 1.71/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.71/0.60  fof(f86,plain,(
% 1.71/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f40])).
% 1.71/0.60  fof(f40,plain,(
% 1.71/0.60    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.71/0.60    inference(ennf_transformation,[],[f9])).
% 1.71/0.60  fof(f9,axiom,(
% 1.71/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.71/0.60  fof(f671,plain,(
% 1.71/0.60    spl4_1 | spl4_43 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_39),
% 1.71/0.60    inference(avatar_split_clause,[],[f670,f573,f139,f134,f129,f124,f119,f114,f660,f100])).
% 1.71/0.60  fof(f660,plain,(
% 1.71/0.60    spl4_43 <=> k1_xboole_0 = sK0),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.71/0.60  fof(f114,plain,(
% 1.71/0.60    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.71/0.60  fof(f119,plain,(
% 1.71/0.60    spl4_5 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.71/0.60  fof(f124,plain,(
% 1.71/0.60    spl4_6 <=> v1_funct_1(sK3)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.71/0.60  fof(f129,plain,(
% 1.71/0.60    spl4_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.71/0.60  fof(f134,plain,(
% 1.71/0.60    spl4_8 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.71/0.60  fof(f139,plain,(
% 1.71/0.60    spl4_9 <=> v1_funct_1(sK2)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.71/0.60  fof(f573,plain,(
% 1.71/0.60    spl4_39 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.71/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.71/0.60  fof(f670,plain,(
% 1.71/0.60    k1_xboole_0 = sK0 | v2_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f669,f141])).
% 1.71/0.60  fof(f141,plain,(
% 1.71/0.60    v1_funct_1(sK2) | ~spl4_9),
% 1.71/0.60    inference(avatar_component_clause,[],[f139])).
% 1.71/0.60  fof(f669,plain,(
% 1.71/0.60    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f668,f136])).
% 1.71/0.60  fof(f136,plain,(
% 1.71/0.60    v1_funct_2(sK2,sK0,sK1) | ~spl4_8),
% 1.71/0.60    inference(avatar_component_clause,[],[f134])).
% 1.71/0.60  fof(f668,plain,(
% 1.71/0.60    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f667,f131])).
% 1.71/0.60  fof(f131,plain,(
% 1.71/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 1.71/0.60    inference(avatar_component_clause,[],[f129])).
% 1.71/0.60  fof(f667,plain,(
% 1.71/0.60    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f666,f126])).
% 1.71/0.60  fof(f126,plain,(
% 1.71/0.60    v1_funct_1(sK3) | ~spl4_6),
% 1.71/0.60    inference(avatar_component_clause,[],[f124])).
% 1.71/0.60  fof(f666,plain,(
% 1.71/0.60    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f665,f121])).
% 1.71/0.60  fof(f121,plain,(
% 1.71/0.60    v1_funct_2(sK3,sK1,sK0) | ~spl4_5),
% 1.71/0.60    inference(avatar_component_clause,[],[f119])).
% 1.71/0.60  fof(f665,plain,(
% 1.71/0.60    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f651,f116])).
% 1.71/0.60  fof(f116,plain,(
% 1.71/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_4),
% 1.71/0.60    inference(avatar_component_clause,[],[f114])).
% 1.71/0.60  fof(f651,plain,(
% 1.71/0.60    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_39),
% 1.71/0.60    inference(subsumption_resolution,[],[f631,f65])).
% 1.71/0.60  fof(f65,plain,(
% 1.71/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.71/0.60    inference(cnf_transformation,[],[f12])).
% 1.71/0.60  fof(f12,axiom,(
% 1.71/0.60    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.71/0.60  fof(f631,plain,(
% 1.71/0.60    ~v2_funct_1(k6_relat_1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_39),
% 1.71/0.60    inference(superposition,[],[f62,f575])).
% 1.71/0.60  fof(f575,plain,(
% 1.71/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_39),
% 1.71/0.60    inference(avatar_component_clause,[],[f573])).
% 1.71/0.60  fof(f62,plain,(
% 1.71/0.60    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f29])).
% 1.71/0.60  fof(f29,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.71/0.60    inference(flattening,[],[f28])).
% 1.71/0.60  fof(f28,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.71/0.60    inference(ennf_transformation,[],[f20])).
% 1.71/0.60  fof(f20,axiom,(
% 1.71/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.71/0.60  fof(f641,plain,(
% 1.71/0.60    spl4_41 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_39),
% 1.71/0.60    inference(avatar_split_clause,[],[f640,f573,f139,f129,f124,f114,f582])).
% 1.71/0.60  fof(f640,plain,(
% 1.71/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f639,f141])).
% 1.71/0.60  fof(f639,plain,(
% 1.71/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f638,f131])).
% 1.71/0.60  fof(f638,plain,(
% 1.71/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f637,f126])).
% 1.71/0.60  fof(f637,plain,(
% 1.71/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_39)),
% 1.71/0.60    inference(subsumption_resolution,[],[f629,f116])).
% 1.71/0.60  fof(f629,plain,(
% 1.71/0.60    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_39),
% 1.71/0.60    inference(superposition,[],[f71,f575])).
% 1.71/0.60  fof(f71,plain,(
% 1.71/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.71/0.60    inference(cnf_transformation,[],[f35])).
% 1.71/0.60  fof(f35,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.71/0.60    inference(flattening,[],[f34])).
% 1.71/0.60  fof(f34,plain,(
% 1.71/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.71/0.60    inference(ennf_transformation,[],[f18])).
% 1.71/0.60  fof(f18,axiom,(
% 1.71/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.71/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.71/0.60  fof(f617,plain,(
% 1.71/0.60    ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_9 | spl4_38),
% 1.71/0.60    inference(avatar_contradiction_clause,[],[f616])).
% 1.71/0.60  fof(f616,plain,(
% 1.71/0.60    $false | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_9 | spl4_38)),
% 1.71/0.60    inference(subsumption_resolution,[],[f615,f141])).
% 1.71/0.60  fof(f615,plain,(
% 1.71/0.60    ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_7 | spl4_38)),
% 1.71/0.60    inference(subsumption_resolution,[],[f614,f131])).
% 1.71/0.60  fof(f614,plain,(
% 1.71/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | spl4_38)),
% 1.71/0.60    inference(subsumption_resolution,[],[f613,f126])).
% 1.71/0.62  fof(f613,plain,(
% 1.71/0.62    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_4 | spl4_38)),
% 1.71/0.62    inference(subsumption_resolution,[],[f608,f116])).
% 1.71/0.62  fof(f608,plain,(
% 1.71/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_38),
% 1.71/0.62    inference(resolution,[],[f571,f70])).
% 1.71/0.62  fof(f70,plain,(
% 1.71/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f33])).
% 1.71/0.62  fof(f33,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.71/0.62    inference(flattening,[],[f32])).
% 1.71/0.62  fof(f32,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.71/0.62    inference(ennf_transformation,[],[f17])).
% 1.71/0.62  fof(f17,axiom,(
% 1.71/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.71/0.62  fof(f571,plain,(
% 1.71/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_38),
% 1.71/0.62    inference(avatar_component_clause,[],[f569])).
% 1.71/0.62  fof(f569,plain,(
% 1.71/0.62    spl4_38 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.71/0.62  fof(f576,plain,(
% 1.71/0.62    ~spl4_38 | spl4_39 | ~spl4_14),
% 1.71/0.62    inference(avatar_split_clause,[],[f564,f167,f573,f569])).
% 1.71/0.62  fof(f167,plain,(
% 1.71/0.62    spl4_14 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.71/0.62  fof(f564,plain,(
% 1.71/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_14),
% 1.71/0.62    inference(resolution,[],[f332,f169])).
% 1.71/0.62  fof(f169,plain,(
% 1.71/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_14),
% 1.71/0.62    inference(avatar_component_clause,[],[f167])).
% 1.71/0.62  fof(f332,plain,(
% 1.71/0.62    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.71/0.62    inference(resolution,[],[f66,f74])).
% 1.71/0.62  fof(f74,plain,(
% 1.71/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.71/0.62    inference(cnf_transformation,[],[f15])).
% 1.71/0.62  fof(f15,axiom,(
% 1.71/0.62    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.71/0.62  fof(f66,plain,(
% 1.71/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.62    inference(cnf_transformation,[],[f46])).
% 1.71/0.62  fof(f46,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.62    inference(nnf_transformation,[],[f31])).
% 1.71/0.62  fof(f31,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.62    inference(flattening,[],[f30])).
% 1.71/0.62  fof(f30,plain,(
% 1.71/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.71/0.62    inference(ennf_transformation,[],[f14])).
% 1.71/0.62  fof(f14,axiom,(
% 1.71/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.71/0.62  fof(f269,plain,(
% 1.71/0.62    spl4_24 | ~spl4_4),
% 1.71/0.62    inference(avatar_split_clause,[],[f260,f114,f266])).
% 1.71/0.62  fof(f260,plain,(
% 1.71/0.62    v5_relat_1(sK3,sK0) | ~spl4_4),
% 1.71/0.62    inference(resolution,[],[f89,f116])).
% 1.71/0.62  fof(f89,plain,(
% 1.71/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f41])).
% 1.71/0.62  fof(f41,plain,(
% 1.71/0.62    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.62    inference(ennf_transformation,[],[f23])).
% 1.71/0.62  fof(f23,plain,(
% 1.71/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.71/0.62    inference(pure_predicate_removal,[],[f13])).
% 1.71/0.62  fof(f13,axiom,(
% 1.71/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.71/0.62  fof(f246,plain,(
% 1.71/0.62    ~spl4_22 | spl4_23 | ~spl4_7),
% 1.71/0.62    inference(avatar_split_clause,[],[f226,f129,f243,f239])).
% 1.71/0.62  fof(f226,plain,(
% 1.71/0.62    v1_xboole_0(sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl4_7),
% 1.71/0.62    inference(resolution,[],[f73,f131])).
% 1.71/0.62  fof(f73,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f37])).
% 1.71/0.62  fof(f37,plain,(
% 1.71/0.62    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.71/0.62    inference(ennf_transformation,[],[f5])).
% 1.71/0.62  fof(f5,axiom,(
% 1.71/0.62    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.71/0.62  fof(f224,plain,(
% 1.71/0.62    spl4_19 | ~spl4_7),
% 1.71/0.62    inference(avatar_split_clause,[],[f219,f129,f221])).
% 1.71/0.62  fof(f219,plain,(
% 1.71/0.62    v1_relat_1(sK2) | ~spl4_7),
% 1.71/0.62    inference(subsumption_resolution,[],[f210,f78])).
% 1.71/0.62  fof(f78,plain,(
% 1.71/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.71/0.62    inference(cnf_transformation,[],[f8])).
% 1.71/0.62  fof(f8,axiom,(
% 1.71/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.71/0.62  fof(f210,plain,(
% 1.71/0.62    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_7),
% 1.71/0.62    inference(resolution,[],[f72,f131])).
% 1.71/0.62  fof(f72,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f36])).
% 1.71/0.62  fof(f36,plain,(
% 1.71/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.71/0.62    inference(ennf_transformation,[],[f6])).
% 1.71/0.62  fof(f6,axiom,(
% 1.71/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.71/0.62  fof(f218,plain,(
% 1.71/0.62    spl4_18 | ~spl4_4),
% 1.71/0.62    inference(avatar_split_clause,[],[f213,f114,f215])).
% 1.71/0.62  fof(f213,plain,(
% 1.71/0.62    v1_relat_1(sK3) | ~spl4_4),
% 1.71/0.62    inference(subsumption_resolution,[],[f209,f78])).
% 1.71/0.62  fof(f209,plain,(
% 1.71/0.62    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_4),
% 1.71/0.62    inference(resolution,[],[f72,f116])).
% 1.71/0.62  fof(f170,plain,(
% 1.71/0.62    spl4_14 | ~spl4_3),
% 1.71/0.62    inference(avatar_split_clause,[],[f165,f109,f167])).
% 1.71/0.62  fof(f109,plain,(
% 1.71/0.62    spl4_3 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.71/0.62  fof(f165,plain,(
% 1.71/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_3),
% 1.71/0.62    inference(backward_demodulation,[],[f111,f68])).
% 1.71/0.62  fof(f68,plain,(
% 1.71/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f19])).
% 1.71/0.62  fof(f19,axiom,(
% 1.71/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.71/0.62  fof(f111,plain,(
% 1.71/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_3),
% 1.71/0.62    inference(avatar_component_clause,[],[f109])).
% 1.71/0.62  fof(f159,plain,(
% 1.71/0.62    spl4_12 | ~spl4_10),
% 1.71/0.62    inference(avatar_split_clause,[],[f153,f144,f156])).
% 1.71/0.62  fof(f144,plain,(
% 1.71/0.62    spl4_10 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.71/0.62  fof(f153,plain,(
% 1.71/0.62    v2_funct_1(k1_xboole_0) | ~spl4_10),
% 1.71/0.62    inference(superposition,[],[f65,f146])).
% 1.71/0.62  fof(f146,plain,(
% 1.71/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl4_10),
% 1.71/0.62    inference(avatar_component_clause,[],[f144])).
% 1.71/0.62  fof(f152,plain,(
% 1.71/0.62    spl4_11),
% 1.71/0.62    inference(avatar_split_clause,[],[f90,f149])).
% 1.71/0.62  fof(f149,plain,(
% 1.71/0.62    spl4_11 <=> v1_xboole_0(k1_xboole_0)),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.71/0.62  fof(f90,plain,(
% 1.71/0.62    v1_xboole_0(k1_xboole_0)),
% 1.71/0.62    inference(cnf_transformation,[],[f1])).
% 1.71/0.62  fof(f1,axiom,(
% 1.71/0.62    v1_xboole_0(k1_xboole_0)),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.71/0.62  fof(f147,plain,(
% 1.71/0.62    spl4_10),
% 1.71/0.62    inference(avatar_split_clause,[],[f83,f144])).
% 1.71/0.62  fof(f83,plain,(
% 1.71/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.71/0.62    inference(cnf_transformation,[],[f11])).
% 1.71/0.62  fof(f11,axiom,(
% 1.71/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.71/0.62  fof(f142,plain,(
% 1.71/0.62    spl4_9),
% 1.71/0.62    inference(avatar_split_clause,[],[f52,f139])).
% 1.71/0.62  fof(f52,plain,(
% 1.71/0.62    v1_funct_1(sK2)),
% 1.71/0.62    inference(cnf_transformation,[],[f44])).
% 1.71/0.62  fof(f44,plain,(
% 1.71/0.62    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.71/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f43,f42])).
% 1.71/0.62  fof(f42,plain,(
% 1.71/0.62    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.71/0.62    introduced(choice_axiom,[])).
% 1.71/0.62  fof(f43,plain,(
% 1.71/0.62    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.71/0.62    introduced(choice_axiom,[])).
% 1.71/0.62  fof(f25,plain,(
% 1.71/0.62    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.71/0.62    inference(flattening,[],[f24])).
% 1.71/0.62  fof(f24,plain,(
% 1.71/0.62    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.71/0.62    inference(ennf_transformation,[],[f22])).
% 1.71/0.62  fof(f22,negated_conjecture,(
% 1.71/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.71/0.62    inference(negated_conjecture,[],[f21])).
% 1.71/0.62  fof(f21,conjecture,(
% 1.71/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.71/0.62  fof(f137,plain,(
% 1.71/0.62    spl4_8),
% 1.71/0.62    inference(avatar_split_clause,[],[f53,f134])).
% 1.71/0.62  fof(f53,plain,(
% 1.71/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.71/0.62    inference(cnf_transformation,[],[f44])).
% 1.71/0.62  fof(f132,plain,(
% 1.71/0.62    spl4_7),
% 1.71/0.62    inference(avatar_split_clause,[],[f54,f129])).
% 1.71/0.62  fof(f54,plain,(
% 1.71/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.62    inference(cnf_transformation,[],[f44])).
% 1.71/0.62  fof(f127,plain,(
% 1.71/0.62    spl4_6),
% 1.71/0.62    inference(avatar_split_clause,[],[f55,f124])).
% 1.71/0.62  fof(f55,plain,(
% 1.71/0.62    v1_funct_1(sK3)),
% 1.71/0.62    inference(cnf_transformation,[],[f44])).
% 1.71/0.62  fof(f122,plain,(
% 1.71/0.62    spl4_5),
% 1.71/0.62    inference(avatar_split_clause,[],[f56,f119])).
% 1.71/0.62  fof(f56,plain,(
% 1.71/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.71/0.62    inference(cnf_transformation,[],[f44])).
% 1.71/0.62  fof(f117,plain,(
% 1.71/0.62    spl4_4),
% 1.71/0.62    inference(avatar_split_clause,[],[f57,f114])).
% 1.71/0.62  fof(f57,plain,(
% 1.71/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.71/0.62    inference(cnf_transformation,[],[f44])).
% 1.71/0.62  fof(f112,plain,(
% 1.71/0.62    spl4_3),
% 1.71/0.62    inference(avatar_split_clause,[],[f58,f109])).
% 1.71/0.62  fof(f58,plain,(
% 1.71/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.71/0.62    inference(cnf_transformation,[],[f44])).
% 1.71/0.62  fof(f107,plain,(
% 1.71/0.62    ~spl4_1 | ~spl4_2),
% 1.71/0.62    inference(avatar_split_clause,[],[f59,f104,f100])).
% 1.71/0.62  fof(f59,plain,(
% 1.71/0.62    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.71/0.62    inference(cnf_transformation,[],[f44])).
% 1.71/0.62  % SZS output end Proof for theBenchmark
% 1.71/0.62  % (3589)------------------------------
% 1.71/0.62  % (3589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.62  % (3589)Termination reason: Refutation
% 1.71/0.62  
% 1.71/0.62  % (3589)Memory used [KB]: 6780
% 1.71/0.62  % (3589)Time elapsed: 0.178 s
% 1.71/0.62  % (3589)------------------------------
% 1.71/0.62  % (3589)------------------------------
% 1.71/0.62  % (3567)Success in time 0.245 s
%------------------------------------------------------------------------------
