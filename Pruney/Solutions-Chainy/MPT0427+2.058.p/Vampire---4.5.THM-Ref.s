%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 232 expanded)
%              Number of leaves         :   35 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  314 ( 615 expanded)
%              Number of equality atoms :   48 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f332,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f86,f135,f139,f159,f172,f186,f196,f241,f242,f247,f251,f255,f260,f268,f273,f292,f294,f323,f331])).

fof(f331,plain,(
    spl3_41 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | spl3_41 ),
    inference(resolution,[],[f322,f68])).

fof(f68,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f37,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f322,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK1)
    | spl3_41 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl3_41
  <=> r1_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f323,plain,
    ( ~ spl3_41
    | spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f313,f106,f84,f321])).

fof(f84,plain,
    ( spl3_8
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f106,plain,
    ( spl3_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f313,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK1)
    | spl3_8
    | ~ spl3_11 ),
    inference(superposition,[],[f85,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f85,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f294,plain,
    ( k1_xboole_0 != sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f292,plain,
    ( ~ spl3_2
    | spl3_7
    | spl3_34 ),
    inference(avatar_split_clause,[],[f289,f271,f81,f53])).

fof(f53,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f81,plain,
    ( spl3_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f271,plain,
    ( spl3_34
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f289,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl3_34 ),
    inference(resolution,[],[f272,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f272,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f271])).

fof(f273,plain,
    ( ~ spl3_34
    | ~ spl3_13
    | spl3_33 ),
    inference(avatar_split_clause,[],[f269,f266,f137,f271])).

fof(f137,plain,
    ( spl3_13
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f266,plain,
    ( spl3_33
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f269,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl3_13
    | spl3_33 ),
    inference(forward_demodulation,[],[f267,f138])).

fof(f138,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f267,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f266])).

fof(f268,plain,
    ( ~ spl3_33
    | spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f188,f133,f49,f266])).

fof(f49,plain,
    ( spl3_1
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f133,plain,
    ( spl3_12
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f188,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_1
    | ~ spl3_12 ),
    inference(superposition,[],[f50,f134])).

fof(f134,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f50,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f260,plain,
    ( ~ spl3_23
    | spl3_31 ),
    inference(avatar_split_clause,[],[f258,f253,f194])).

fof(f194,plain,
    ( spl3_23
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f253,plain,
    ( spl3_31
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f258,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl3_31 ),
    inference(resolution,[],[f254,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f254,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( ~ spl3_25
    | ~ spl3_31
    | spl3_22 ),
    inference(avatar_split_clause,[],[f211,f184,f253,f218])).

fof(f218,plain,
    ( spl3_25
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f184,plain,
    ( spl3_22
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f211,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_22 ),
    inference(superposition,[],[f185,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f185,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f184])).

fof(f251,plain,(
    spl3_30 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl3_30 ),
    inference(resolution,[],[f246,f116])).

fof(f116,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f115,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f40,f47])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f246,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl3_30
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f247,plain,
    ( ~ spl3_30
    | spl3_29 ),
    inference(avatar_split_clause,[],[f243,f239,f245])).

fof(f239,plain,
    ( spl3_29
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f243,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_29 ),
    inference(resolution,[],[f240,f43])).

fof(f240,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f239])).

fof(f242,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f241,plain,
    ( ~ spl3_25
    | ~ spl3_29
    | spl3_16 ),
    inference(avatar_split_clause,[],[f237,f157,f239,f218])).

fof(f157,plain,
    ( spl3_16
  <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f237,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_16 ),
    inference(superposition,[],[f158,f47])).

fof(f158,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f196,plain,
    ( ~ spl3_3
    | spl3_23
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f189,f133,f194,f57])).

fof(f57,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f189,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_12 ),
    inference(superposition,[],[f40,f134])).

fof(f186,plain,
    ( ~ spl3_22
    | ~ spl3_12
    | spl3_19 ),
    inference(avatar_split_clause,[],[f182,f170,f133,f184])).

fof(f170,plain,
    ( spl3_19
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f182,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_12
    | spl3_19 ),
    inference(forward_demodulation,[],[f171,f134])).

fof(f171,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,
    ( ~ spl3_19
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f143,f81,f49,f170])).

fof(f143,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_7 ),
    inference(superposition,[],[f50,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f159,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f155,f106,f81,f49,f157])).

fof(f155,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f143,f107])).

fof(f139,plain,
    ( spl3_13
    | spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f127,f61,f81,f137])).

fof(f61,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f125,f62])).

fof(f62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f41,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f135,plain,
    ( spl3_12
    | spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f126,f57,f106,f133])).

fof(f126,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f125,f58])).

fof(f58,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f86,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f78,f53,f84,f81])).

fof(f78,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(resolution,[],[f77,f54])).

fof(f54,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

% (10473)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f63,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f59,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f49])).

fof(f32,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:29:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (10467)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (10459)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (10465)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (10465)Refutation not found, incomplete strategy% (10465)------------------------------
% 0.21/0.48  % (10465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10465)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10465)Memory used [KB]: 6012
% 0.21/0.48  % (10465)Time elapsed: 0.060 s
% 0.21/0.48  % (10465)------------------------------
% 0.21/0.48  % (10465)------------------------------
% 0.21/0.48  % (10458)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (10459)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f86,f135,f139,f159,f172,f186,f196,f241,f242,f247,f251,f255,f260,f268,f273,f292,f294,f323,f331])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    spl3_41),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    $false | spl3_41),
% 0.21/0.49    inference(resolution,[],[f322,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(superposition,[],[f37,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    ~r1_xboole_0(k1_xboole_0,sK1) | spl3_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f321])).
% 0.21/0.49  fof(f321,plain,(
% 0.21/0.49    spl3_41 <=> r1_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    ~spl3_41 | spl3_8 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f313,f106,f84,f321])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl3_8 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl3_11 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ~r1_xboole_0(k1_xboole_0,sK1) | (spl3_8 | ~spl3_11)),
% 0.21/0.49    inference(superposition,[],[f85,f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f106])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ~r1_xboole_0(sK2,sK1) | spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f84])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    k1_xboole_0 != sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f292,plain,(
% 0.21/0.49    ~spl3_2 | spl3_7 | spl3_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f289,f271,f81,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl3_7 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    spl3_34 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl3_34),
% 0.21/0.49    inference(resolution,[],[f272,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f271])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ~spl3_34 | ~spl3_13 | spl3_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f269,f266,f137,f271])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl3_13 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    spl3_33 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl3_13 | spl3_33)),
% 0.21/0.49    inference(forward_demodulation,[],[f267,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | spl3_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f266])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ~spl3_33 | spl3_1 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f188,f133,f49,f266])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl3_1 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl3_12 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl3_1 | ~spl3_12)),
% 0.21/0.49    inference(superposition,[],[f50,f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f133])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ~spl3_23 | spl3_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f258,f253,f194])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl3_23 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    spl3_31 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | spl3_31),
% 0.21/0.49    inference(resolution,[],[f254,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl3_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f253])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ~spl3_25 | ~spl3_31 | spl3_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f211,f184,f253,f218])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl3_25 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    spl3_22 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_22),
% 0.21/0.49    inference(superposition,[],[f185,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl3_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f184])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    spl3_30),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f249])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    $false | spl3_30),
% 0.21/0.49    inference(resolution,[],[f246,f116])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(resolution,[],[f115,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(superposition,[],[f40,f47])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f245])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    spl3_30 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ~spl3_30 | spl3_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f243,f239,f245])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    spl3_29 <=> r1_tarski(sK0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_29),
% 0.21/0.49    inference(resolution,[],[f240,f43])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK0) | spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f239])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ~spl3_25 | ~spl3_29 | spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f237,f157,f239,f218])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl3_16 <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_16),
% 0.21/0.49    inference(superposition,[],[f158,f47])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f157])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ~spl3_3 | spl3_23 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f189,f133,f194,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_12),
% 0.21/0.49    inference(superposition,[],[f40,f134])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    ~spl3_22 | ~spl3_12 | spl3_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f182,f170,f133,f184])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl3_19 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (~spl3_12 | spl3_19)),
% 0.21/0.49    inference(forward_demodulation,[],[f171,f134])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ~spl3_19 | spl3_1 | ~spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f143,f81,f49,f170])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_7)),
% 0.21/0.49    inference(superposition,[],[f50,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ~spl3_16 | spl3_1 | ~spl3_7 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f155,f106,f81,f49,f157])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_7 | ~spl3_11)),
% 0.21/0.49    inference(forward_demodulation,[],[f143,f107])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl3_13 | spl3_7 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f127,f61,f81,f137])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_4),
% 0.21/0.49    inference(resolution,[],[f125,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.21/0.49    inference(superposition,[],[f41,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl3_12 | spl3_11 | ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f57,f106,f133])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_3),
% 0.21/0.49    inference(resolution,[],[f125,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl3_7 | ~spl3_8 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f53,f84,f81])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~r1_xboole_0(sK2,sK1) | k1_xboole_0 = sK1 | ~spl3_2),
% 0.21/0.49    inference(resolution,[],[f77,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.49    inference(resolution,[],[f45,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  % (10473)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f61])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f26,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f57])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f53])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f49])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10459)------------------------------
% 0.21/0.49  % (10459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10459)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10459)Memory used [KB]: 10746
% 0.21/0.49  % (10459)Time elapsed: 0.015 s
% 0.21/0.49  % (10459)------------------------------
% 0.21/0.49  % (10459)------------------------------
% 0.21/0.49  % (10450)Success in time 0.132 s
%------------------------------------------------------------------------------
