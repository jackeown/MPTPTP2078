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
% DateTime   : Thu Dec  3 12:46:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 239 expanded)
%              Number of leaves         :   34 ( 106 expanded)
%              Depth                    :    8
%              Number of atoms          :  321 ( 646 expanded)
%              Number of equality atoms :   49 ( 128 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f74,f79,f142,f149,f162,f167,f197,f211,f228,f321,f375,f387,f390,f396,f465,f475,f480,f483,f486])).

fof(f486,plain,
    ( sK1 != sK2
    | k8_setfam_1(sK0,sK1) != k1_setfam_1(sK1)
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f483,plain,
    ( ~ spl3_45
    | spl3_59 ),
    inference(avatar_split_clause,[],[f481,f478,f365])).

fof(f365,plain,
    ( spl3_45
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f478,plain,
    ( spl3_59
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f481,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_59 ),
    inference(resolution,[],[f479,f86])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f35,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f479,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_59 ),
    inference(avatar_component_clause,[],[f478])).

fof(f480,plain,
    ( ~ spl3_59
    | spl3_58 ),
    inference(avatar_split_clause,[],[f476,f473,f478])).

fof(f473,plain,
    ( spl3_58
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f476,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_58 ),
    inference(resolution,[],[f474,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f474,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_58 ),
    inference(avatar_component_clause,[],[f473])).

fof(f475,plain,
    ( ~ spl3_45
    | ~ spl3_58
    | spl3_56 ),
    inference(avatar_split_clause,[],[f467,f463,f473,f365])).

fof(f463,plain,
    ( spl3_56
  <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f467,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_56 ),
    inference(superposition,[],[f464,f42])).

fof(f464,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)
    | spl3_56 ),
    inference(avatar_component_clause,[],[f463])).

fof(f465,plain,
    ( ~ spl3_45
    | ~ spl3_56
    | ~ spl3_16
    | spl3_38 ),
    inference(avatar_split_clause,[],[f461,f281,f140,f463,f365])).

fof(f140,plain,
    ( spl3_16
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f281,plain,
    ( spl3_38
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f461,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_16
    | spl3_38 ),
    inference(forward_demodulation,[],[f460,f141])).

fof(f141,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f460,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_38 ),
    inference(superposition,[],[f282,f42])).

fof(f282,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f281])).

fof(f396,plain,
    ( ~ spl3_38
    | spl3_1
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f288,f147,f44,f281])).

fof(f44,plain,
    ( spl3_1
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f147,plain,
    ( spl3_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f288,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_18 ),
    inference(superposition,[],[f45,f148])).

fof(f148,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f147])).

fof(f45,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f390,plain,
    ( ~ spl3_21
    | spl3_49 ),
    inference(avatar_split_clause,[],[f388,f385,f165])).

fof(f165,plain,
    ( spl3_21
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f385,plain,
    ( spl3_49
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f388,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl3_49 ),
    inference(resolution,[],[f386,f39])).

fof(f386,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_49 ),
    inference(avatar_component_clause,[],[f385])).

fof(f387,plain,
    ( ~ spl3_45
    | ~ spl3_49
    | spl3_30 ),
    inference(avatar_split_clause,[],[f383,f226,f385,f365])).

fof(f226,plain,
    ( spl3_30
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f383,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_30 ),
    inference(superposition,[],[f227,f42])).

fof(f227,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f226])).

fof(f375,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f321,plain,(
    spl3_26 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl3_26 ),
    inference(resolution,[],[f196,f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f196,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl3_26
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f228,plain,
    ( ~ spl3_30
    | spl3_1
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f224,f147,f137,f44,f226])).

fof(f137,plain,
    ( spl3_15
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f224,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f215,f138])).

fof(f138,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f215,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_18 ),
    inference(superposition,[],[f45,f148])).

fof(f211,plain,
    ( ~ spl3_2
    | spl3_18
    | spl3_20 ),
    inference(avatar_split_clause,[],[f208,f160,f147,f48])).

fof(f48,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f160,plain,
    ( spl3_20
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f208,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl3_20 ),
    inference(resolution,[],[f161,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f161,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f197,plain,
    ( ~ spl3_26
    | spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f173,f140,f77,f195])).

fof(f77,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f173,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl3_8
    | ~ spl3_16 ),
    inference(superposition,[],[f78,f141])).

fof(f78,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f167,plain,
    ( ~ spl3_3
    | spl3_21
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f152,f137,f165,f52])).

fof(f52,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f152,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_15 ),
    inference(superposition,[],[f35,f138])).

fof(f162,plain,
    ( ~ spl3_20
    | spl3_1
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f158,f144,f137,f44,f160])).

fof(f144,plain,
    ( spl3_17
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f158,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_1
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f151,f145])).

fof(f145,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f151,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_1
    | ~ spl3_15 ),
    inference(superposition,[],[f45,f138])).

fof(f149,plain,
    ( spl3_17
    | spl3_18
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f131,f56,f147,f144])).

fof(f56,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f131,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f121,f57])).

fof(f57,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f121,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f142,plain,
    ( spl3_15
    | spl3_16
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f130,f52,f140,f137])).

fof(f130,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f121,f53])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f79,plain,
    ( ~ spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f75,f69,f77])).

fof(f69,plain,
    ( spl3_6
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f75,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | spl3_6 ),
    inference(resolution,[],[f70,f39])).

fof(f70,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f74,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f66,f48,f72,f69])).

fof(f72,plain,
    ( spl3_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f66,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f58,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f54,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f46,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f44])).

% (8379)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f31,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:19:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.48  % (8368)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.48  % (8384)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.49  % (8373)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.23/0.49  % (8376)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.49  % (8378)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.50  % (8382)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.50  % (8382)Refutation not found, incomplete strategy% (8382)------------------------------
% 0.23/0.50  % (8382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (8382)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (8382)Memory used [KB]: 6012
% 0.23/0.50  % (8382)Time elapsed: 0.095 s
% 0.23/0.50  % (8382)------------------------------
% 0.23/0.50  % (8382)------------------------------
% 0.23/0.50  % (8388)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.23/0.50  % (8386)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.23/0.50  % (8383)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.23/0.50  % (8376)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f487,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f74,f79,f142,f149,f162,f167,f197,f211,f228,f321,f375,f387,f390,f396,f465,f475,f480,f483,f486])).
% 0.23/0.51  fof(f486,plain,(
% 0.23/0.51    sK1 != sK2 | k8_setfam_1(sK0,sK1) != k1_setfam_1(sK1) | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.23/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.51  fof(f483,plain,(
% 0.23/0.51    ~spl3_45 | spl3_59),
% 0.23/0.51    inference(avatar_split_clause,[],[f481,f478,f365])).
% 0.23/0.51  fof(f365,plain,(
% 0.23/0.51    spl3_45 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.23/0.51  fof(f478,plain,(
% 0.23/0.51    spl3_59 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.23/0.51  fof(f481,plain,(
% 0.23/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_59),
% 0.23/0.51    inference(resolution,[],[f479,f86])).
% 0.23/0.51  fof(f86,plain,(
% 0.23/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f85])).
% 0.23/0.51  fof(f85,plain,(
% 0.23/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.23/0.51    inference(superposition,[],[f35,f42])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.23/0.51    inference(equality_resolution,[],[f37])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.23/0.51    inference(ennf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.23/0.51    inference(ennf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.23/0.51  fof(f479,plain,(
% 0.23/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_59),
% 0.23/0.51    inference(avatar_component_clause,[],[f478])).
% 0.23/0.51  fof(f480,plain,(
% 0.23/0.51    ~spl3_59 | spl3_58),
% 0.23/0.51    inference(avatar_split_clause,[],[f476,f473,f478])).
% 0.23/0.51  fof(f473,plain,(
% 0.23/0.51    spl3_58 <=> r1_tarski(sK0,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.23/0.51  fof(f476,plain,(
% 0.23/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_58),
% 0.23/0.51    inference(resolution,[],[f474,f39])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.51    inference(nnf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.51  fof(f474,plain,(
% 0.23/0.51    ~r1_tarski(sK0,sK0) | spl3_58),
% 0.23/0.51    inference(avatar_component_clause,[],[f473])).
% 0.23/0.51  fof(f475,plain,(
% 0.23/0.51    ~spl3_45 | ~spl3_58 | spl3_56),
% 0.23/0.51    inference(avatar_split_clause,[],[f467,f463,f473,f365])).
% 0.23/0.51  fof(f463,plain,(
% 0.23/0.51    spl3_56 <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.23/0.51  fof(f467,plain,(
% 0.23/0.51    ~r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_56),
% 0.23/0.51    inference(superposition,[],[f464,f42])).
% 0.23/0.51  fof(f464,plain,(
% 0.23/0.51    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) | spl3_56),
% 0.23/0.51    inference(avatar_component_clause,[],[f463])).
% 0.23/0.51  fof(f465,plain,(
% 0.23/0.51    ~spl3_45 | ~spl3_56 | ~spl3_16 | spl3_38),
% 0.23/0.51    inference(avatar_split_clause,[],[f461,f281,f140,f463,f365])).
% 0.23/0.51  fof(f140,plain,(
% 0.23/0.51    spl3_16 <=> k1_xboole_0 = sK2),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.23/0.51  fof(f281,plain,(
% 0.23/0.51    spl3_38 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.23/0.51  fof(f461,plain,(
% 0.23/0.51    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_16 | spl3_38)),
% 0.23/0.51    inference(forward_demodulation,[],[f460,f141])).
% 0.23/0.51  fof(f141,plain,(
% 0.23/0.51    k1_xboole_0 = sK2 | ~spl3_16),
% 0.23/0.51    inference(avatar_component_clause,[],[f140])).
% 0.23/0.51  fof(f460,plain,(
% 0.23/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_38),
% 0.23/0.51    inference(superposition,[],[f282,f42])).
% 0.23/0.51  fof(f282,plain,(
% 0.23/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl3_38),
% 0.23/0.51    inference(avatar_component_clause,[],[f281])).
% 0.23/0.51  fof(f396,plain,(
% 0.23/0.51    ~spl3_38 | spl3_1 | ~spl3_18),
% 0.23/0.51    inference(avatar_split_clause,[],[f288,f147,f44,f281])).
% 0.23/0.51  fof(f44,plain,(
% 0.23/0.51    spl3_1 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.51  fof(f147,plain,(
% 0.23/0.51    spl3_18 <=> k1_xboole_0 = sK1),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.23/0.51  fof(f288,plain,(
% 0.23/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_18)),
% 0.23/0.51    inference(superposition,[],[f45,f148])).
% 0.23/0.51  fof(f148,plain,(
% 0.23/0.51    k1_xboole_0 = sK1 | ~spl3_18),
% 0.23/0.51    inference(avatar_component_clause,[],[f147])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_1),
% 0.23/0.51    inference(avatar_component_clause,[],[f44])).
% 0.23/0.51  fof(f390,plain,(
% 0.23/0.51    ~spl3_21 | spl3_49),
% 0.23/0.51    inference(avatar_split_clause,[],[f388,f385,f165])).
% 0.23/0.51  fof(f165,plain,(
% 0.23/0.51    spl3_21 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.23/0.51  fof(f385,plain,(
% 0.23/0.51    spl3_49 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.23/0.51  fof(f388,plain,(
% 0.23/0.51    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | spl3_49),
% 0.23/0.51    inference(resolution,[],[f386,f39])).
% 0.23/0.51  fof(f386,plain,(
% 0.23/0.51    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl3_49),
% 0.23/0.51    inference(avatar_component_clause,[],[f385])).
% 0.23/0.51  fof(f387,plain,(
% 0.23/0.51    ~spl3_45 | ~spl3_49 | spl3_30),
% 0.23/0.51    inference(avatar_split_clause,[],[f383,f226,f385,f365])).
% 0.23/0.51  fof(f226,plain,(
% 0.23/0.51    spl3_30 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.23/0.51  fof(f383,plain,(
% 0.23/0.51    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_30),
% 0.23/0.51    inference(superposition,[],[f227,f42])).
% 0.23/0.51  fof(f227,plain,(
% 0.23/0.51    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl3_30),
% 0.23/0.51    inference(avatar_component_clause,[],[f226])).
% 0.23/0.51  fof(f375,plain,(
% 0.23/0.51    k1_xboole_0 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.51  fof(f321,plain,(
% 0.23/0.51    spl3_26),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f318])).
% 0.23/0.51  fof(f318,plain,(
% 0.23/0.51    $false | spl3_26),
% 0.23/0.51    inference(resolution,[],[f196,f32])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.23/0.51  fof(f196,plain,(
% 0.23/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl3_26),
% 0.23/0.51    inference(avatar_component_clause,[],[f195])).
% 0.23/0.51  fof(f195,plain,(
% 0.23/0.51    spl3_26 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.23/0.51  fof(f228,plain,(
% 0.23/0.51    ~spl3_30 | spl3_1 | ~spl3_15 | ~spl3_18),
% 0.23/0.51    inference(avatar_split_clause,[],[f224,f147,f137,f44,f226])).
% 0.23/0.51  fof(f137,plain,(
% 0.23/0.51    spl3_15 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.23/0.51  fof(f224,plain,(
% 0.23/0.51    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_15 | ~spl3_18)),
% 0.23/0.51    inference(forward_demodulation,[],[f215,f138])).
% 0.23/0.51  fof(f138,plain,(
% 0.23/0.51    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_15),
% 0.23/0.51    inference(avatar_component_clause,[],[f137])).
% 0.23/0.51  fof(f215,plain,(
% 0.23/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_18)),
% 0.23/0.51    inference(superposition,[],[f45,f148])).
% 0.23/0.51  fof(f211,plain,(
% 0.23/0.51    ~spl3_2 | spl3_18 | spl3_20),
% 0.23/0.51    inference(avatar_split_clause,[],[f208,f160,f147,f48])).
% 0.23/0.51  fof(f48,plain,(
% 0.23/0.51    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.51  fof(f160,plain,(
% 0.23/0.51    spl3_20 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.23/0.51  fof(f208,plain,(
% 0.23/0.51    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl3_20),
% 0.23/0.51    inference(resolution,[],[f161,f33])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.51    inference(flattening,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.23/0.51  fof(f161,plain,(
% 0.23/0.51    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_20),
% 0.23/0.51    inference(avatar_component_clause,[],[f160])).
% 0.23/0.51  fof(f197,plain,(
% 0.23/0.51    ~spl3_26 | spl3_8 | ~spl3_16),
% 0.23/0.51    inference(avatar_split_clause,[],[f173,f140,f77,f195])).
% 0.23/0.51  fof(f77,plain,(
% 0.23/0.51    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.51  fof(f173,plain,(
% 0.23/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | (spl3_8 | ~spl3_16)),
% 0.23/0.51    inference(superposition,[],[f78,f141])).
% 0.23/0.51  fof(f78,plain,(
% 0.23/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | spl3_8),
% 0.23/0.51    inference(avatar_component_clause,[],[f77])).
% 0.23/0.51  fof(f167,plain,(
% 0.23/0.51    ~spl3_3 | spl3_21 | ~spl3_15),
% 0.23/0.51    inference(avatar_split_clause,[],[f152,f137,f165,f52])).
% 0.23/0.51  fof(f52,plain,(
% 0.23/0.51    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.51  fof(f152,plain,(
% 0.23/0.51    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_15),
% 0.23/0.51    inference(superposition,[],[f35,f138])).
% 0.23/0.51  fof(f162,plain,(
% 0.23/0.51    ~spl3_20 | spl3_1 | ~spl3_15 | ~spl3_17),
% 0.23/0.51    inference(avatar_split_clause,[],[f158,f144,f137,f44,f160])).
% 0.23/0.51  fof(f144,plain,(
% 0.23/0.51    spl3_17 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.23/0.51  fof(f158,plain,(
% 0.23/0.51    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl3_1 | ~spl3_15 | ~spl3_17)),
% 0.23/0.51    inference(forward_demodulation,[],[f151,f145])).
% 0.23/0.51  fof(f145,plain,(
% 0.23/0.51    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_17),
% 0.23/0.51    inference(avatar_component_clause,[],[f144])).
% 0.23/0.51  fof(f151,plain,(
% 0.23/0.51    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl3_1 | ~spl3_15)),
% 0.23/0.51    inference(superposition,[],[f45,f138])).
% 0.23/0.51  fof(f149,plain,(
% 0.23/0.51    spl3_17 | spl3_18 | ~spl3_4),
% 0.23/0.51    inference(avatar_split_clause,[],[f131,f56,f147,f144])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.51  fof(f131,plain,(
% 0.23/0.51    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_4),
% 0.23/0.51    inference(resolution,[],[f121,f57])).
% 0.23/0.51  fof(f57,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.23/0.51    inference(avatar_component_clause,[],[f56])).
% 0.23/0.51  fof(f121,plain,(
% 0.23/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f118])).
% 0.23/0.51  fof(f118,plain,(
% 0.23/0.51    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.23/0.51    inference(superposition,[],[f36,f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f142,plain,(
% 0.23/0.51    spl3_15 | spl3_16 | ~spl3_3),
% 0.23/0.51    inference(avatar_split_clause,[],[f130,f52,f140,f137])).
% 0.23/0.51  fof(f130,plain,(
% 0.23/0.51    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_3),
% 0.23/0.51    inference(resolution,[],[f121,f53])).
% 0.23/0.51  fof(f53,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f52])).
% 0.23/0.51  fof(f79,plain,(
% 0.23/0.51    ~spl3_8 | spl3_6),
% 0.23/0.51    inference(avatar_split_clause,[],[f75,f69,f77])).
% 0.23/0.51  fof(f69,plain,(
% 0.23/0.51    spl3_6 <=> r1_tarski(sK2,sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.51  fof(f75,plain,(
% 0.23/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | spl3_6),
% 0.23/0.51    inference(resolution,[],[f70,f39])).
% 0.23/0.51  fof(f70,plain,(
% 0.23/0.51    ~r1_tarski(sK2,sK1) | spl3_6),
% 0.23/0.51    inference(avatar_component_clause,[],[f69])).
% 0.23/0.51  fof(f74,plain,(
% 0.23/0.51    ~spl3_6 | spl3_7 | ~spl3_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f66,f48,f72,f69])).
% 0.23/0.51  fof(f72,plain,(
% 0.23/0.51    spl3_7 <=> sK1 = sK2),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.51  fof(f66,plain,(
% 0.23/0.51    sK1 = sK2 | ~r1_tarski(sK2,sK1) | ~spl3_2),
% 0.23/0.51    inference(resolution,[],[f65,f49])).
% 0.23/0.51  fof(f49,plain,(
% 0.23/0.51    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f48])).
% 0.23/0.51  fof(f65,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~r1_tarski(X1,X0)) )),
% 0.23/0.51    inference(resolution,[],[f38,f41])).
% 0.23/0.51  fof(f41,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.51    inference(flattening,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f12])).
% 0.23/0.51  fof(f12,plain,(
% 0.23/0.51    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.23/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.23/0.51  fof(f58,plain,(
% 0.23/0.51    spl3_4),
% 0.23/0.51    inference(avatar_split_clause,[],[f28,f56])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.51    inference(cnf_transformation,[],[f26])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f25,f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.23/0.51    inference(flattening,[],[f14])).
% 0.23/0.51  fof(f14,plain,(
% 0.23/0.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.23/0.51    inference(ennf_transformation,[],[f11])).
% 0.23/0.51  fof(f11,negated_conjecture,(
% 0.23/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.23/0.51    inference(negated_conjecture,[],[f10])).
% 0.23/0.51  fof(f10,conjecture,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.23/0.51  fof(f54,plain,(
% 0.23/0.51    spl3_3),
% 0.23/0.51    inference(avatar_split_clause,[],[f29,f52])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.51    inference(cnf_transformation,[],[f26])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    spl3_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f30,f48])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    r1_tarski(sK1,sK2)),
% 0.23/0.51    inference(cnf_transformation,[],[f26])).
% 0.23/0.51  fof(f46,plain,(
% 0.23/0.51    ~spl3_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f31,f44])).
% 0.23/0.51  % (8379)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.23/0.51    inference(cnf_transformation,[],[f26])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (8376)------------------------------
% 0.23/0.51  % (8376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (8376)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (8376)Memory used [KB]: 10874
% 0.23/0.51  % (8376)Time elapsed: 0.021 s
% 0.23/0.51  % (8376)------------------------------
% 0.23/0.51  % (8376)------------------------------
% 0.23/0.51  % (8370)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.51  % (8383)Refutation not found, incomplete strategy% (8383)------------------------------
% 0.23/0.51  % (8383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (8383)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (8383)Memory used [KB]: 1663
% 0.23/0.51  % (8383)Time elapsed: 0.084 s
% 0.23/0.51  % (8383)------------------------------
% 0.23/0.51  % (8383)------------------------------
% 0.23/0.51  % (8361)Success in time 0.143 s
%------------------------------------------------------------------------------
