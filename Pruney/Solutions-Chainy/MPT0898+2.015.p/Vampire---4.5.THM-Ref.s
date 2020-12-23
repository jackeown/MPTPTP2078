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
% DateTime   : Thu Dec  3 12:59:17 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 323 expanded)
%              Number of leaves         :   36 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :  365 ( 694 expanded)
%              Number of equality atoms :  139 ( 288 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1092,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f333,f506,f631,f633,f789,f835,f901,f910,f938,f943,f964,f967,f1053,f1056,f1085,f1091])).

fof(f1091,plain,
    ( spl3_44
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f1090,f1082,f935])).

fof(f935,plain,
    ( spl3_44
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1082,plain,
    ( spl3_52
  <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f1090,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_52 ),
    inference(trivial_inequality_removal,[],[f1089])).

fof(f1089,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ spl3_52 ),
    inference(duplicate_literal_removal,[],[f1088])).

fof(f1088,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | ~ spl3_52 ),
    inference(superposition,[],[f63,f1084])).

fof(f1084,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

fof(f1085,plain,
    ( spl3_24
    | spl3_44
    | spl3_52
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f1080,f242,f102,f97,f1082,f935,f496])).

fof(f496,plain,
    ( spl3_24
  <=> ! [X0] : k1_xboole_0 = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f97,plain,
    ( spl3_2
  <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f102,plain,
    ( spl3_3
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f242,plain,
    ( spl3_10
  <=> k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1080,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = X0 )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f1079])).

fof(f1079,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = X0 )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f63,f482])).

fof(f482,plain,
    ( ! [X29] : k1_xboole_0 = k3_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0,X29)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f481])).

fof(f481,plain,
    ( ! [X29] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0,X29) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f80,f471])).

fof(f471,plain,
    ( ! [X6,X7] : k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0,X6),X7)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f181,f299])).

fof(f299,plain,
    ( ! [X8,X9] : k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X8),X9)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f298,f147])).

fof(f147,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl3_3 ),
    inference(resolution,[],[f146,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f146,plain,
    ( ! [X0,X1] : r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,X1))
    | ~ spl3_3 ),
    inference(resolution,[],[f72,f104])).

fof(f104,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f298,plain,
    ( ! [X8,X9] : k2_zfmisc_1(k1_xboole_0,X9) = k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X8),X9)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f295,f147])).

fof(f295,plain,
    ( ! [X8,X9] : k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X8),X9) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8),X9)
    | ~ spl3_10 ),
    inference(superposition,[],[f86,f244])).

fof(f244,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f242])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f181,plain,
    ( ! [X6,X7] : k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X6),X7) = k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0,X6),X7)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f172,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(definition_unfolding,[],[f68,f67])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).

fof(f172,plain,
    ( ! [X6,X7] : k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X6),X7) = k3_zfmisc_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),X6,X7)
    | ~ spl3_2 ),
    inference(superposition,[],[f85,f99])).

fof(f99,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f50,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f1056,plain,
    ( ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f837,f137,f124])).

fof(f124,plain,
    ( spl3_4
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f137,plain,
    ( spl3_7
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f837,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f138,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f138,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f1053,plain,
    ( spl3_25
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1051,f503,f499])).

fof(f499,plain,
    ( spl3_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f503,plain,
    ( spl3_26
  <=> k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1051,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_26 ),
    inference(trivial_inequality_removal,[],[f1050])).

fof(f1050,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ spl3_26 ),
    inference(duplicate_literal_removal,[],[f1049])).

fof(f1049,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ spl3_26 ),
    inference(superposition,[],[f63,f505])).

fof(f505,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f503])).

fof(f967,plain,
    ( spl3_4
    | ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f965,f92,f128,f124])).

fof(f128,plain,
    ( spl3_5
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f965,plain,
    ( ~ r1_tarski(sK0,sK1)
    | r2_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(extensionality_resolution,[],[f56,f94])).

fof(f94,plain,
    ( sK0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f964,plain,(
    ~ spl3_45 ),
    inference(avatar_contradiction_clause,[],[f963])).

fof(f963,plain,
    ( $false
    | ~ spl3_45 ),
    inference(resolution,[],[f942,f346])).

fof(f346,plain,(
    ! [X5] : ~ r2_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f108,f336])).

fof(f336,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f303,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f303,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(X0,k1_xboole_0),X0)
      | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f55,f301])).

fof(f301,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f78,f79])).

fof(f79,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f42,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f78,plain,(
    ! [X0] : k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f41,f75])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f49,f74])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f108,plain,(
    ! [X0,X1] : ~ r2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f59,f47])).

fof(f942,plain,
    ( r2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f940])).

fof(f940,plain,
    ( spl3_45
  <=> r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f943,plain,
    ( spl3_45
    | ~ spl3_4
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f928,f499,f124,f940])).

fof(f928,plain,
    ( r2_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f126,f501])).

fof(f501,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f499])).

fof(f126,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f938,plain,
    ( ~ spl3_44
    | spl3_1
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f927,f499,f92,f935])).

fof(f927,plain,
    ( k1_xboole_0 != sK0
    | spl3_1
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f94,f501])).

fof(f910,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f236,f229,f97,f242])).

fof(f229,plain,
    ( spl3_8
  <=> k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f236,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f99,f231])).

fof(f231,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f229])).

fof(f901,plain,
    ( spl3_5
    | spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f896,f97,f229,f128])).

fof(f896,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f284,f106])).

fof(f106,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f284,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(k2_zfmisc_1(X12,X13),k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0))
        | k1_xboole_0 = k2_zfmisc_1(X12,X13)
        | r1_tarski(X13,sK1) )
    | ~ spl3_2 ),
    inference(superposition,[],[f71,f99])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f835,plain,
    ( spl3_7
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f830,f286,f137])).

fof(f286,plain,
    ( spl3_15
  <=> ! [X13,X12] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X12,X13))
        | r1_tarski(sK1,X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f830,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_15 ),
    inference(resolution,[],[f287,f106])).

fof(f287,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X12,X13))
        | r1_tarski(sK1,X13) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f286])).

fof(f789,plain,
    ( spl3_8
    | spl3_15
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f784,f97,f286,f229])).

fof(f784,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X12,X13))
        | k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)
        | r1_tarski(sK1,X13) )
    | ~ spl3_2 ),
    inference(superposition,[],[f71,f99])).

fof(f633,plain,
    ( ~ spl3_17
    | spl3_5
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f632,f496,f128,f322])).

fof(f322,plain,
    ( spl3_17
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f632,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_5
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f572,f497])).

fof(f497,plain,
    ( ! [X0] : k1_xboole_0 = X0
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f496])).

fof(f572,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl3_5
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f130,f497])).

fof(f130,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f631,plain,
    ( ~ spl3_17
    | spl3_7
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f630,f496,f137,f322])).

fof(f630,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_7
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f571,f497])).

fof(f571,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl3_7
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f139,f497])).

fof(f139,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f506,plain,
    ( spl3_24
    | spl3_25
    | spl3_26
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f494,f242,f102,f503,f499,f496])).

fof(f494,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = X0 )
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f493])).

fof(f493,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1)
        | k1_xboole_0 = sK1
        | k1_xboole_0 = X0 )
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f63,f373])).

fof(f373,plain,
    ( ! [X25] : k1_xboole_0 = k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X25)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f372])).

fof(f372,plain,
    ( ! [X25] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X25) )
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f80,f299])).

fof(f333,plain,(
    spl3_17 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl3_17 ),
    inference(resolution,[],[f324,f106])).

fof(f324,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f322])).

fof(f105,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f87,f102])).

fof(f87,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f77,f97])).

fof(f77,plain,(
    k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1) ),
    inference(definition_unfolding,[],[f39,f67,f67])).

fof(f39,plain,(
    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

fof(f95,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f92])).

fof(f40,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (3819)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (3811)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (3803)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (3812)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (3804)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (3812)Refutation not found, incomplete strategy% (3812)------------------------------
% 0.21/0.53  % (3812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3820)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (3820)Refutation not found, incomplete strategy% (3820)------------------------------
% 0.21/0.53  % (3820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3812)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3812)Memory used [KB]: 6140
% 0.21/0.53  % (3812)Time elapsed: 0.122 s
% 0.21/0.53  % (3812)------------------------------
% 0.21/0.53  % (3812)------------------------------
% 0.21/0.53  % (3801)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (3797)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (3820)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3820)Memory used [KB]: 1663
% 0.21/0.53  % (3820)Time elapsed: 0.120 s
% 0.21/0.53  % (3820)------------------------------
% 0.21/0.53  % (3820)------------------------------
% 0.21/0.54  % (3802)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (3825)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (3798)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (3800)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (3822)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (3799)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3826)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (3821)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (3815)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (3814)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (3817)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (3814)Refutation not found, incomplete strategy% (3814)------------------------------
% 0.21/0.55  % (3814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3814)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3814)Memory used [KB]: 10618
% 0.21/0.55  % (3814)Time elapsed: 0.145 s
% 0.21/0.55  % (3814)------------------------------
% 0.21/0.55  % (3814)------------------------------
% 0.21/0.55  % (3818)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (3817)Refutation not found, incomplete strategy% (3817)------------------------------
% 0.21/0.55  % (3817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3817)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3817)Memory used [KB]: 10746
% 0.21/0.55  % (3817)Time elapsed: 0.147 s
% 0.21/0.55  % (3817)------------------------------
% 0.21/0.55  % (3817)------------------------------
% 0.21/0.55  % (3813)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (3806)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (3807)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (3808)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (3807)Refutation not found, incomplete strategy% (3807)------------------------------
% 0.21/0.55  % (3807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3807)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (3807)Memory used [KB]: 10618
% 0.21/0.55  % (3807)Time elapsed: 0.142 s
% 0.21/0.55  % (3807)------------------------------
% 0.21/0.55  % (3807)------------------------------
% 0.21/0.55  % (3805)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (3824)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (3809)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (3805)Refutation not found, incomplete strategy% (3805)------------------------------
% 0.21/0.56  % (3805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3805)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3805)Memory used [KB]: 10746
% 0.21/0.56  % (3805)Time elapsed: 0.148 s
% 0.21/0.56  % (3805)------------------------------
% 0.21/0.56  % (3805)------------------------------
% 0.21/0.56  % (3823)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (3810)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (3797)Refutation not found, incomplete strategy% (3797)------------------------------
% 0.21/0.56  % (3797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3797)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3797)Memory used [KB]: 1791
% 0.21/0.56  % (3797)Time elapsed: 0.152 s
% 0.21/0.56  % (3797)------------------------------
% 0.21/0.56  % (3797)------------------------------
% 0.21/0.56  % (3816)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.74/0.61  % (3813)Refutation found. Thanks to Tanya!
% 1.74/0.61  % SZS status Theorem for theBenchmark
% 1.97/0.62  % SZS output start Proof for theBenchmark
% 1.97/0.62  fof(f1092,plain,(
% 1.97/0.62    $false),
% 1.97/0.62    inference(avatar_sat_refutation,[],[f95,f100,f105,f333,f506,f631,f633,f789,f835,f901,f910,f938,f943,f964,f967,f1053,f1056,f1085,f1091])).
% 1.97/0.62  fof(f1091,plain,(
% 1.97/0.62    spl3_44 | ~spl3_52),
% 1.97/0.62    inference(avatar_split_clause,[],[f1090,f1082,f935])).
% 1.97/0.62  fof(f935,plain,(
% 1.97/0.62    spl3_44 <=> k1_xboole_0 = sK0),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.97/0.62  fof(f1082,plain,(
% 1.97/0.62    spl3_52 <=> k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.97/0.62  fof(f1090,plain,(
% 1.97/0.62    k1_xboole_0 = sK0 | ~spl3_52),
% 1.97/0.62    inference(trivial_inequality_removal,[],[f1089])).
% 1.97/0.62  fof(f1089,plain,(
% 1.97/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | ~spl3_52),
% 1.97/0.62    inference(duplicate_literal_removal,[],[f1088])).
% 1.97/0.62  fof(f1088,plain,(
% 1.97/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | ~spl3_52),
% 1.97/0.62    inference(superposition,[],[f63,f1084])).
% 1.97/0.62  fof(f1084,plain,(
% 1.97/0.62    k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) | ~spl3_52),
% 1.97/0.62    inference(avatar_component_clause,[],[f1082])).
% 1.97/0.62  fof(f63,plain,(
% 1.97/0.62    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 1.97/0.62    inference(cnf_transformation,[],[f20])).
% 1.97/0.62  fof(f20,axiom,(
% 1.97/0.62    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).
% 1.97/0.62  fof(f1085,plain,(
% 1.97/0.62    spl3_24 | spl3_44 | spl3_52 | ~spl3_2 | ~spl3_3 | ~spl3_10),
% 1.97/0.62    inference(avatar_split_clause,[],[f1080,f242,f102,f97,f1082,f935,f496])).
% 1.97/0.62  fof(f496,plain,(
% 1.97/0.62    spl3_24 <=> ! [X0] : k1_xboole_0 = X0),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.97/0.62  fof(f97,plain,(
% 1.97/0.62    spl3_2 <=> k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.97/0.62  fof(f102,plain,(
% 1.97/0.62    spl3_3 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.97/0.62  fof(f242,plain,(
% 1.97/0.62    spl3_10 <=> k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.97/0.62  fof(f1080,plain,(
% 1.97/0.62    ( ! [X0] : (k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = X0) ) | (~spl3_2 | ~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(trivial_inequality_removal,[],[f1079])).
% 1.97/0.62  fof(f1079,plain,(
% 1.97/0.62    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_zfmisc_1(sK0,sK0,sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = X0) ) | (~spl3_2 | ~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(superposition,[],[f63,f482])).
% 1.97/0.62  fof(f482,plain,(
% 1.97/0.62    ( ! [X29] : (k1_xboole_0 = k3_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0,X29)) ) | (~spl3_2 | ~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(trivial_inequality_removal,[],[f481])).
% 1.97/0.62  fof(f481,plain,(
% 1.97/0.62    ( ! [X29] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0,X29)) ) | (~spl3_2 | ~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(superposition,[],[f80,f471])).
% 1.97/0.62  fof(f471,plain,(
% 1.97/0.62    ( ! [X6,X7] : (k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0,X6),X7)) ) | (~spl3_2 | ~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(forward_demodulation,[],[f181,f299])).
% 1.97/0.62  fof(f299,plain,(
% 1.97/0.62    ( ! [X8,X9] : (k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X8),X9)) ) | (~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(forward_demodulation,[],[f298,f147])).
% 1.97/0.62  fof(f147,plain,(
% 1.97/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | ~spl3_3),
% 1.97/0.62    inference(resolution,[],[f146,f44])).
% 1.97/0.62  fof(f44,plain,(
% 1.97/0.62    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.97/0.62    inference(cnf_transformation,[],[f29])).
% 1.97/0.62  fof(f29,plain,(
% 1.97/0.62    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.97/0.62    inference(ennf_transformation,[],[f11])).
% 1.97/0.62  fof(f11,axiom,(
% 1.97/0.62    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.97/0.62  fof(f146,plain,(
% 1.97/0.62    ( ! [X0,X1] : (r1_xboole_0(k2_zfmisc_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,X1))) ) | ~spl3_3),
% 1.97/0.62    inference(resolution,[],[f72,f104])).
% 1.97/0.62  fof(f104,plain,(
% 1.97/0.62    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_3),
% 1.97/0.62    inference(avatar_component_clause,[],[f102])).
% 1.97/0.62  fof(f72,plain,(
% 1.97/0.62    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.97/0.62    inference(cnf_transformation,[],[f38])).
% 1.97/0.62  fof(f38,plain,(
% 1.97/0.62    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 1.97/0.62    inference(ennf_transformation,[],[f15])).
% 1.97/0.62  fof(f15,axiom,(
% 1.97/0.62    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 1.97/0.62  fof(f298,plain,(
% 1.97/0.62    ( ! [X8,X9] : (k2_zfmisc_1(k1_xboole_0,X9) = k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X8),X9)) ) | (~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(forward_demodulation,[],[f295,f147])).
% 1.97/0.62  fof(f295,plain,(
% 1.97/0.62    ( ! [X8,X9] : (k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X8),X9) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8),X9)) ) | ~spl3_10),
% 1.97/0.62    inference(superposition,[],[f86,f244])).
% 1.97/0.62  fof(f244,plain,(
% 1.97/0.62    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1) | ~spl3_10),
% 1.97/0.62    inference(avatar_component_clause,[],[f242])).
% 1.97/0.62  fof(f86,plain,(
% 1.97/0.62    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.97/0.62    inference(definition_unfolding,[],[f69,f67])).
% 1.97/0.62  fof(f67,plain,(
% 1.97/0.62    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f19])).
% 1.97/0.62  fof(f19,axiom,(
% 1.97/0.62    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 1.97/0.62  fof(f69,plain,(
% 1.97/0.62    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f21])).
% 1.97/0.62  fof(f21,axiom,(
% 1.97/0.62    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_mcart_1)).
% 1.97/0.62  fof(f181,plain,(
% 1.97/0.62    ( ! [X6,X7] : (k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X6),X7) = k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0,X6),X7)) ) | ~spl3_2),
% 1.97/0.62    inference(forward_demodulation,[],[f172,f85])).
% 1.97/0.62  fof(f85,plain,(
% 1.97/0.62    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) )),
% 1.97/0.62    inference(definition_unfolding,[],[f68,f67])).
% 1.97/0.62  fof(f68,plain,(
% 1.97/0.62    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f22])).
% 1.97/0.62  fof(f22,axiom,(
% 1.97/0.62    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).
% 1.97/0.62  fof(f172,plain,(
% 1.97/0.62    ( ! [X6,X7] : (k2_zfmisc_1(k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X6),X7) = k3_zfmisc_1(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),X6,X7)) ) | ~spl3_2),
% 1.97/0.62    inference(superposition,[],[f85,f99])).
% 1.97/0.62  fof(f99,plain,(
% 1.97/0.62    k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1) | ~spl3_2),
% 1.97/0.62    inference(avatar_component_clause,[],[f97])).
% 1.97/0.62  fof(f80,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0) )),
% 1.97/0.62    inference(definition_unfolding,[],[f54,f76])).
% 1.97/0.62  fof(f76,plain,(
% 1.97/0.62    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.97/0.62    inference(definition_unfolding,[],[f43,f50])).
% 1.97/0.62  fof(f50,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f13])).
% 1.97/0.62  fof(f13,axiom,(
% 1.97/0.62    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_enumset1)).
% 1.97/0.62  fof(f43,plain,(
% 1.97/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f12])).
% 1.97/0.62  fof(f12,axiom,(
% 1.97/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.97/0.62  fof(f54,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))) )),
% 1.97/0.62    inference(cnf_transformation,[],[f31])).
% 1.97/0.62  fof(f31,plain,(
% 1.97/0.62    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 1.97/0.62    inference(ennf_transformation,[],[f16])).
% 1.97/0.62  fof(f16,axiom,(
% 1.97/0.62    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 1.97/0.62  fof(f1056,plain,(
% 1.97/0.62    ~spl3_4 | ~spl3_7),
% 1.97/0.62    inference(avatar_split_clause,[],[f837,f137,f124])).
% 1.97/0.62  fof(f124,plain,(
% 1.97/0.62    spl3_4 <=> r2_xboole_0(sK0,sK1)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.97/0.62  fof(f137,plain,(
% 1.97/0.62    spl3_7 <=> r1_tarski(sK1,sK0)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.97/0.62  fof(f837,plain,(
% 1.97/0.62    ~r2_xboole_0(sK0,sK1) | ~spl3_7),
% 1.97/0.62    inference(resolution,[],[f138,f59])).
% 1.97/0.62  fof(f59,plain,(
% 1.97/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f35])).
% 1.97/0.62  fof(f35,plain,(
% 1.97/0.62    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 1.97/0.62    inference(ennf_transformation,[],[f10])).
% 1.97/0.62  fof(f10,axiom,(
% 1.97/0.62    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 1.97/0.62  fof(f138,plain,(
% 1.97/0.62    r1_tarski(sK1,sK0) | ~spl3_7),
% 1.97/0.62    inference(avatar_component_clause,[],[f137])).
% 1.97/0.62  fof(f1053,plain,(
% 1.97/0.62    spl3_25 | ~spl3_26),
% 1.97/0.62    inference(avatar_split_clause,[],[f1051,f503,f499])).
% 1.97/0.62  fof(f499,plain,(
% 1.97/0.62    spl3_25 <=> k1_xboole_0 = sK1),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.97/0.62  fof(f503,plain,(
% 1.97/0.62    spl3_26 <=> k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.97/0.62  fof(f1051,plain,(
% 1.97/0.62    k1_xboole_0 = sK1 | ~spl3_26),
% 1.97/0.62    inference(trivial_inequality_removal,[],[f1050])).
% 1.97/0.62  fof(f1050,plain,(
% 1.97/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~spl3_26),
% 1.97/0.62    inference(duplicate_literal_removal,[],[f1049])).
% 1.97/0.62  fof(f1049,plain,(
% 1.97/0.62    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~spl3_26),
% 1.97/0.62    inference(superposition,[],[f63,f505])).
% 1.97/0.62  fof(f505,plain,(
% 1.97/0.62    k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1) | ~spl3_26),
% 1.97/0.62    inference(avatar_component_clause,[],[f503])).
% 1.97/0.62  fof(f967,plain,(
% 1.97/0.62    spl3_4 | ~spl3_5 | spl3_1),
% 1.97/0.62    inference(avatar_split_clause,[],[f965,f92,f128,f124])).
% 1.97/0.62  fof(f128,plain,(
% 1.97/0.62    spl3_5 <=> r1_tarski(sK0,sK1)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.97/0.62  fof(f92,plain,(
% 1.97/0.62    spl3_1 <=> sK0 = sK1),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.97/0.62  fof(f965,plain,(
% 1.97/0.62    ~r1_tarski(sK0,sK1) | r2_xboole_0(sK0,sK1) | spl3_1),
% 1.97/0.62    inference(extensionality_resolution,[],[f56,f94])).
% 1.97/0.62  fof(f94,plain,(
% 1.97/0.62    sK0 != sK1 | spl3_1),
% 1.97/0.62    inference(avatar_component_clause,[],[f92])).
% 1.97/0.62  fof(f56,plain,(
% 1.97/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f34])).
% 1.97/0.62  fof(f34,plain,(
% 1.97/0.62    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.97/0.62    inference(flattening,[],[f33])).
% 1.97/0.62  fof(f33,plain,(
% 1.97/0.62    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 1.97/0.62    inference(ennf_transformation,[],[f27])).
% 1.97/0.62  fof(f27,plain,(
% 1.97/0.62    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 1.97/0.62    inference(unused_predicate_definition_removal,[],[f2])).
% 1.97/0.62  fof(f2,axiom,(
% 1.97/0.62    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.97/0.62  fof(f964,plain,(
% 1.97/0.62    ~spl3_45),
% 1.97/0.62    inference(avatar_contradiction_clause,[],[f963])).
% 1.97/0.62  fof(f963,plain,(
% 1.97/0.62    $false | ~spl3_45),
% 1.97/0.62    inference(resolution,[],[f942,f346])).
% 1.97/0.62  fof(f346,plain,(
% 1.97/0.62    ( ! [X5] : (~r2_xboole_0(X5,k1_xboole_0)) )),
% 1.97/0.62    inference(superposition,[],[f108,f336])).
% 1.97/0.62  fof(f336,plain,(
% 1.97/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.97/0.62    inference(resolution,[],[f303,f47])).
% 1.97/0.62  fof(f47,plain,(
% 1.97/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f6])).
% 1.97/0.62  fof(f6,axiom,(
% 1.97/0.62    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.97/0.62  fof(f303,plain,(
% 1.97/0.62    ( ! [X0] : (~r1_tarski(k3_xboole_0(X0,k1_xboole_0),X0) | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.97/0.62    inference(superposition,[],[f55,f301])).
% 1.97/0.62  fof(f301,plain,(
% 1.97/0.62    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.97/0.62    inference(forward_demodulation,[],[f78,f79])).
% 1.97/0.62  fof(f79,plain,(
% 1.97/0.62    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.97/0.62    inference(definition_unfolding,[],[f42,f74])).
% 1.97/0.62  fof(f74,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.97/0.62    inference(definition_unfolding,[],[f48,f50])).
% 1.97/0.62  fof(f48,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.97/0.62    inference(cnf_transformation,[],[f14])).
% 1.97/0.62  fof(f14,axiom,(
% 1.97/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.97/0.62  fof(f42,plain,(
% 1.97/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.97/0.62    inference(cnf_transformation,[],[f7])).
% 1.97/0.62  fof(f7,axiom,(
% 1.97/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.97/0.62  fof(f78,plain,(
% 1.97/0.62    ( ! [X0] : (k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)),k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.97/0.62    inference(definition_unfolding,[],[f41,f75])).
% 1.97/0.62  fof(f75,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,X1))) )),
% 1.97/0.62    inference(definition_unfolding,[],[f49,f74])).
% 1.97/0.62  fof(f49,plain,(
% 1.97/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.97/0.62    inference(cnf_transformation,[],[f5])).
% 1.97/0.62  fof(f5,axiom,(
% 1.97/0.62    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 1.97/0.62  fof(f41,plain,(
% 1.97/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.97/0.62    inference(cnf_transformation,[],[f9])).
% 1.97/0.62  fof(f9,axiom,(
% 1.97/0.62    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.97/0.62  fof(f55,plain,(
% 1.97/0.62    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 1.97/0.62    inference(cnf_transformation,[],[f32])).
% 1.97/0.62  fof(f32,plain,(
% 1.97/0.62    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 1.97/0.62    inference(ennf_transformation,[],[f8])).
% 1.97/0.62  fof(f8,axiom,(
% 1.97/0.62    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 1.97/0.62  fof(f108,plain,(
% 1.97/0.62    ( ! [X0,X1] : (~r2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.97/0.62    inference(resolution,[],[f59,f47])).
% 1.97/0.62  fof(f942,plain,(
% 1.97/0.62    r2_xboole_0(sK0,k1_xboole_0) | ~spl3_45),
% 1.97/0.62    inference(avatar_component_clause,[],[f940])).
% 1.97/0.62  fof(f940,plain,(
% 1.97/0.62    spl3_45 <=> r2_xboole_0(sK0,k1_xboole_0)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.97/0.62  fof(f943,plain,(
% 1.97/0.62    spl3_45 | ~spl3_4 | ~spl3_25),
% 1.97/0.62    inference(avatar_split_clause,[],[f928,f499,f124,f940])).
% 1.97/0.62  fof(f928,plain,(
% 1.97/0.62    r2_xboole_0(sK0,k1_xboole_0) | (~spl3_4 | ~spl3_25)),
% 1.97/0.62    inference(backward_demodulation,[],[f126,f501])).
% 1.97/0.62  fof(f501,plain,(
% 1.97/0.62    k1_xboole_0 = sK1 | ~spl3_25),
% 1.97/0.62    inference(avatar_component_clause,[],[f499])).
% 1.97/0.62  fof(f126,plain,(
% 1.97/0.62    r2_xboole_0(sK0,sK1) | ~spl3_4),
% 1.97/0.62    inference(avatar_component_clause,[],[f124])).
% 1.97/0.62  fof(f938,plain,(
% 1.97/0.62    ~spl3_44 | spl3_1 | ~spl3_25),
% 1.97/0.62    inference(avatar_split_clause,[],[f927,f499,f92,f935])).
% 1.97/0.62  fof(f927,plain,(
% 1.97/0.62    k1_xboole_0 != sK0 | (spl3_1 | ~spl3_25)),
% 1.97/0.62    inference(backward_demodulation,[],[f94,f501])).
% 1.97/0.62  fof(f910,plain,(
% 1.97/0.62    spl3_10 | ~spl3_2 | ~spl3_8),
% 1.97/0.62    inference(avatar_split_clause,[],[f236,f229,f97,f242])).
% 1.97/0.62  fof(f229,plain,(
% 1.97/0.62    spl3_8 <=> k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.97/0.62  fof(f236,plain,(
% 1.97/0.62    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1) | (~spl3_2 | ~spl3_8)),
% 1.97/0.62    inference(backward_demodulation,[],[f99,f231])).
% 1.97/0.62  fof(f231,plain,(
% 1.97/0.62    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) | ~spl3_8),
% 1.97/0.62    inference(avatar_component_clause,[],[f229])).
% 1.97/0.62  fof(f901,plain,(
% 1.97/0.62    spl3_5 | spl3_8 | ~spl3_2),
% 1.97/0.62    inference(avatar_split_clause,[],[f896,f97,f229,f128])).
% 1.97/0.62  fof(f896,plain,(
% 1.97/0.62    k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) | r1_tarski(sK0,sK1) | ~spl3_2),
% 1.97/0.62    inference(resolution,[],[f284,f106])).
% 1.97/0.62  fof(f106,plain,(
% 1.97/0.62    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.97/0.62    inference(superposition,[],[f47,f46])).
% 1.97/0.62  fof(f46,plain,(
% 1.97/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.97/0.62    inference(cnf_transformation,[],[f25])).
% 1.97/0.62  fof(f25,plain,(
% 1.97/0.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.97/0.62    inference(rectify,[],[f3])).
% 1.97/0.62  fof(f3,axiom,(
% 1.97/0.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.97/0.62  fof(f284,plain,(
% 1.97/0.62    ( ! [X12,X13] : (~r1_tarski(k2_zfmisc_1(X12,X13),k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0)) | k1_xboole_0 = k2_zfmisc_1(X12,X13) | r1_tarski(X13,sK1)) ) | ~spl3_2),
% 1.97/0.62    inference(superposition,[],[f71,f99])).
% 1.97/0.62  fof(f71,plain,(
% 1.97/0.62    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | r1_tarski(X1,X3)) )),
% 1.97/0.62    inference(cnf_transformation,[],[f37])).
% 1.97/0.62  fof(f37,plain,(
% 1.97/0.62    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.97/0.62    inference(flattening,[],[f36])).
% 1.97/0.62  fof(f36,plain,(
% 1.97/0.62    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 1.97/0.62    inference(ennf_transformation,[],[f17])).
% 1.97/0.62  fof(f17,axiom,(
% 1.97/0.62    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 1.97/0.62  fof(f835,plain,(
% 1.97/0.62    spl3_7 | ~spl3_15),
% 1.97/0.62    inference(avatar_split_clause,[],[f830,f286,f137])).
% 1.97/0.62  fof(f286,plain,(
% 1.97/0.62    spl3_15 <=> ! [X13,X12] : (~r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X12,X13)) | r1_tarski(sK1,X13))),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.97/0.62  fof(f830,plain,(
% 1.97/0.62    r1_tarski(sK1,sK0) | ~spl3_15),
% 1.97/0.62    inference(resolution,[],[f287,f106])).
% 1.97/0.62  fof(f287,plain,(
% 1.97/0.62    ( ! [X12,X13] : (~r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X12,X13)) | r1_tarski(sK1,X13)) ) | ~spl3_15),
% 1.97/0.62    inference(avatar_component_clause,[],[f286])).
% 1.97/0.62  fof(f789,plain,(
% 1.97/0.62    spl3_8 | spl3_15 | ~spl3_2),
% 1.97/0.62    inference(avatar_split_clause,[],[f784,f97,f286,f229])).
% 1.97/0.62  fof(f784,plain,(
% 1.97/0.62    ( ! [X12,X13] : (~r1_tarski(k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0),k2_zfmisc_1(X12,X13)) | k1_xboole_0 = k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) | r1_tarski(sK1,X13)) ) | ~spl3_2),
% 1.97/0.62    inference(superposition,[],[f71,f99])).
% 1.97/0.62  fof(f633,plain,(
% 1.97/0.62    ~spl3_17 | spl3_5 | ~spl3_24),
% 1.97/0.62    inference(avatar_split_clause,[],[f632,f496,f128,f322])).
% 1.97/0.62  fof(f322,plain,(
% 1.97/0.62    spl3_17 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.97/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.97/0.62  fof(f632,plain,(
% 1.97/0.62    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl3_5 | ~spl3_24)),
% 1.97/0.62    inference(forward_demodulation,[],[f572,f497])).
% 1.97/0.62  fof(f497,plain,(
% 1.97/0.62    ( ! [X0] : (k1_xboole_0 = X0) ) | ~spl3_24),
% 1.97/0.62    inference(avatar_component_clause,[],[f496])).
% 1.97/0.62  fof(f572,plain,(
% 1.97/0.62    ~r1_tarski(k1_xboole_0,sK1) | (spl3_5 | ~spl3_24)),
% 1.97/0.62    inference(backward_demodulation,[],[f130,f497])).
% 1.97/0.62  fof(f130,plain,(
% 1.97/0.62    ~r1_tarski(sK0,sK1) | spl3_5),
% 1.97/0.62    inference(avatar_component_clause,[],[f128])).
% 1.97/0.62  fof(f631,plain,(
% 1.97/0.62    ~spl3_17 | spl3_7 | ~spl3_24),
% 1.97/0.62    inference(avatar_split_clause,[],[f630,f496,f137,f322])).
% 1.97/0.62  fof(f630,plain,(
% 1.97/0.62    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl3_7 | ~spl3_24)),
% 1.97/0.62    inference(forward_demodulation,[],[f571,f497])).
% 1.97/0.62  fof(f571,plain,(
% 1.97/0.62    ~r1_tarski(sK1,k1_xboole_0) | (spl3_7 | ~spl3_24)),
% 1.97/0.62    inference(backward_demodulation,[],[f139,f497])).
% 1.97/0.62  fof(f139,plain,(
% 1.97/0.62    ~r1_tarski(sK1,sK0) | spl3_7),
% 1.97/0.62    inference(avatar_component_clause,[],[f137])).
% 1.97/0.62  fof(f506,plain,(
% 1.97/0.62    spl3_24 | spl3_25 | spl3_26 | ~spl3_3 | ~spl3_10),
% 1.97/0.62    inference(avatar_split_clause,[],[f494,f242,f102,f503,f499,f496])).
% 1.97/0.62  fof(f494,plain,(
% 1.97/0.62    ( ! [X0] : (k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = X0) ) | (~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(trivial_inequality_removal,[],[f493])).
% 1.97/0.62  fof(f493,plain,(
% 1.97/0.62    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_zfmisc_1(sK1,sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = X0) ) | (~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(superposition,[],[f63,f373])).
% 1.97/0.62  fof(f373,plain,(
% 1.97/0.62    ( ! [X25] : (k1_xboole_0 = k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X25)) ) | (~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(trivial_inequality_removal,[],[f372])).
% 1.97/0.62  fof(f372,plain,(
% 1.97/0.62    ( ! [X25] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1,X25)) ) | (~spl3_3 | ~spl3_10)),
% 1.97/0.62    inference(superposition,[],[f80,f299])).
% 1.97/0.62  fof(f333,plain,(
% 1.97/0.62    spl3_17),
% 1.97/0.62    inference(avatar_contradiction_clause,[],[f332])).
% 1.97/0.62  fof(f332,plain,(
% 1.97/0.62    $false | spl3_17),
% 1.97/0.62    inference(resolution,[],[f324,f106])).
% 1.97/0.62  fof(f324,plain,(
% 1.97/0.62    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl3_17),
% 1.97/0.62    inference(avatar_component_clause,[],[f322])).
% 1.97/0.62  fof(f105,plain,(
% 1.97/0.62    spl3_3),
% 1.97/0.62    inference(avatar_split_clause,[],[f87,f102])).
% 1.97/0.62  fof(f87,plain,(
% 1.97/0.62    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.97/0.62    inference(equality_resolution,[],[f45])).
% 1.97/0.62  fof(f45,plain,(
% 1.97/0.62    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 1.97/0.62    inference(cnf_transformation,[],[f29])).
% 1.97/0.62  fof(f100,plain,(
% 1.97/0.62    spl3_2),
% 1.97/0.62    inference(avatar_split_clause,[],[f77,f97])).
% 1.97/0.62  fof(f77,plain,(
% 1.97/0.62    k2_zfmisc_1(k3_zfmisc_1(sK0,sK0,sK0),sK0) = k2_zfmisc_1(k3_zfmisc_1(sK1,sK1,sK1),sK1)),
% 1.97/0.62    inference(definition_unfolding,[],[f39,f67,f67])).
% 1.97/0.62  fof(f39,plain,(
% 1.97/0.62    k4_zfmisc_1(sK0,sK0,sK0,sK0) = k4_zfmisc_1(sK1,sK1,sK1,sK1)),
% 1.97/0.62    inference(cnf_transformation,[],[f28])).
% 1.97/0.62  fof(f28,plain,(
% 1.97/0.62    ? [X0,X1] : (X0 != X1 & k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1))),
% 1.97/0.62    inference(ennf_transformation,[],[f24])).
% 1.97/0.62  fof(f24,negated_conjecture,(
% 1.97/0.62    ~! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 1.97/0.62    inference(negated_conjecture,[],[f23])).
% 1.97/0.62  fof(f23,conjecture,(
% 1.97/0.62    ! [X0,X1] : (k4_zfmisc_1(X0,X0,X0,X0) = k4_zfmisc_1(X1,X1,X1,X1) => X0 = X1)),
% 1.97/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).
% 1.97/0.62  fof(f95,plain,(
% 1.97/0.62    ~spl3_1),
% 1.97/0.62    inference(avatar_split_clause,[],[f40,f92])).
% 1.97/0.62  fof(f40,plain,(
% 1.97/0.62    sK0 != sK1),
% 1.97/0.62    inference(cnf_transformation,[],[f28])).
% 1.97/0.62  % SZS output end Proof for theBenchmark
% 1.97/0.62  % (3813)------------------------------
% 1.97/0.62  % (3813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.97/0.62  % (3813)Termination reason: Refutation
% 1.97/0.62  
% 1.97/0.62  % (3813)Memory used [KB]: 11257
% 1.97/0.62  % (3813)Time elapsed: 0.191 s
% 1.97/0.62  % (3813)------------------------------
% 1.97/0.62  % (3813)------------------------------
% 1.97/0.62  % (3796)Success in time 0.262 s
%------------------------------------------------------------------------------
