%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:22 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 338 expanded)
%              Number of leaves         :   25 ( 124 expanded)
%              Depth                    :   15
%              Number of atoms          :  266 ( 660 expanded)
%              Number of equality atoms :   84 ( 268 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1047,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f76,f106,f135,f140,f152,f351,f356,f426,f464,f1046])).

fof(f1046,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_19
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f1045])).

fof(f1045,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_19
    | spl3_20 ),
    inference(subsumption_resolution,[],[f1044,f474])).

fof(f474,plain,
    ( ! [X1] : k7_subset_1(sK0,sK1,X1) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))
    | ~ spl3_1
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f473,f154])).

fof(f154,plain,
    ( ! [X0] : k7_subset_1(sK0,sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))
    | ~ spl3_1 ),
    inference(superposition,[],[f97,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f97,plain,
    ( ! [X0] : k7_subset_1(sK0,sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f35,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f41,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f473,plain,
    ( ! [X1] : k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f466,f27])).

fof(f466,plain,
    ( ! [X1] : k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(k5_xboole_0(sK0,X1),sK1)
    | ~ spl3_19 ),
    inference(superposition,[],[f33,f425])).

fof(f425,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl3_19
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f1044,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13
    | spl3_20 ),
    inference(superposition,[],[f463,f446])).

fof(f446,plain,
    ( ! [X0] : k3_xboole_0(X0,k5_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X0,k5_xboole_0(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f121,f442])).

fof(f442,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f151,f441])).

fof(f441,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f334,f440])).

fof(f440,plain,
    ( sK2 = k5_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f129,f435])).

fof(f435,plain,
    ( k3_subset_1(sK0,sK2) = k3_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_13 ),
    inference(superposition,[],[f60,f355])).

fof(f355,plain,
    ( k3_subset_1(sK0,sK2) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl3_13
  <=> k3_subset_1(sK0,sK2) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f129,plain,
    ( sK2 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f120,f56])).

fof(f56,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f120,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f105,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f105,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_5
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f334,plain,
    ( sK2 = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f328,f139])).

fof(f139,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_7
  <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f328,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f105,f308])).

fof(f308,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ) ),
    inference(backward_demodulation,[],[f36,f296])).

fof(f296,plain,(
    ! [X2,X1] : k3_xboole_0(X2,k5_xboole_0(X2,X1)) = k5_xboole_0(X2,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f90,f27])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f82,f27])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f33,f26])).

fof(f151,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_9
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f121,plain,
    ( ! [X0] : k3_xboole_0(X0,k3_subset_1(sK0,sK2)) = k9_subset_1(sK0,X0,k3_subset_1(sK0,sK2))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f105,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f463,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl3_20
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f464,plain,
    ( ~ spl3_20
    | ~ spl3_2
    | spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f443,f353,f149,f137,f103,f49,f44,f461])).

fof(f49,plain,
    ( spl3_3
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f443,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | ~ spl3_2
    | spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f51,f442])).

fof(f51,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f426,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f366,f348,f132,f73,f39,f423])).

fof(f73,plain,
    ( spl3_4
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f132,plain,
    ( spl3_6
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f348,plain,
    ( spl3_12
  <=> k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f366,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f335,f365])).

fof(f365,plain,
    ( sK1 = k5_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f117,f360])).

fof(f360,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_12 ),
    inference(superposition,[],[f60,f350])).

fof(f350,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f348])).

fof(f117,plain,
    ( sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f108,f55])).

fof(f55,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f41,f31])).

fof(f108,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f75,f36])).

fof(f75,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f335,plain,
    ( sK1 = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_subset_1(sK0,sK1)))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f327,f134])).

fof(f134,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f327,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_subset_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f75,f308])).

fof(f356,plain,
    ( spl3_13
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f326,f44,f353])).

fof(f326,plain,
    ( k3_subset_1(sK0,sK2) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f46,f308])).

fof(f351,plain,
    ( spl3_12
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f325,f39,f348])).

fof(f325,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f41,f308])).

fof(f152,plain,
    ( spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f93,f44,f149])).

fof(f93,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f46,f36])).

fof(f140,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f44,f137])).

fof(f135,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f55,f39,f132])).

fof(f106,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f54,f44,f103])).

fof(f54,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f76,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f53,f39,f73])).

fof(f53,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f41,f29])).

fof(f52,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (2119)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.42  % (2119)Refutation not found, incomplete strategy% (2119)------------------------------
% 0.20/0.42  % (2119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (2119)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.42  
% 0.20/0.42  % (2119)Memory used [KB]: 10618
% 0.20/0.42  % (2119)Time elapsed: 0.006 s
% 0.20/0.42  % (2119)------------------------------
% 0.20/0.42  % (2119)------------------------------
% 0.20/0.44  % (2108)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (2120)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (2115)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (2109)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (2111)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (2124)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (2122)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (2117)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (2110)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (2118)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (2114)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (2112)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (2121)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.51  % (2113)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.51  % (2116)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.52  % (2123)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.52  % (2125)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.65/0.60  % (2123)Refutation found. Thanks to Tanya!
% 1.65/0.60  % SZS status Theorem for theBenchmark
% 1.65/0.60  % SZS output start Proof for theBenchmark
% 1.65/0.60  fof(f1047,plain,(
% 1.65/0.60    $false),
% 1.65/0.60    inference(avatar_sat_refutation,[],[f42,f47,f52,f76,f106,f135,f140,f152,f351,f356,f426,f464,f1046])).
% 1.65/0.60  fof(f1046,plain,(
% 1.65/0.60    ~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_19 | spl3_20),
% 1.65/0.60    inference(avatar_contradiction_clause,[],[f1045])).
% 1.65/0.60  fof(f1045,plain,(
% 1.65/0.60    $false | (~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13 | ~spl3_19 | spl3_20)),
% 1.65/0.60    inference(subsumption_resolution,[],[f1044,f474])).
% 1.65/0.60  fof(f474,plain,(
% 1.65/0.60    ( ! [X1] : (k7_subset_1(sK0,sK1,X1) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))) ) | (~spl3_1 | ~spl3_19)),
% 1.65/0.60    inference(forward_demodulation,[],[f473,f154])).
% 1.65/0.60  fof(f154,plain,(
% 1.65/0.60    ( ! [X0] : (k7_subset_1(sK0,sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) ) | ~spl3_1),
% 1.65/0.60    inference(superposition,[],[f97,f27])).
% 1.65/0.60  fof(f27,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f1])).
% 1.65/0.60  fof(f1,axiom,(
% 1.65/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.65/0.60  fof(f97,plain,(
% 1.65/0.60    ( ! [X0] : (k7_subset_1(sK0,sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ) | ~spl3_1),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f41,f37])).
% 1.65/0.60  fof(f37,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 1.65/0.60    inference(definition_unfolding,[],[f35,f28])).
% 1.65/0.60  fof(f28,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f3])).
% 1.65/0.60  fof(f3,axiom,(
% 1.65/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.65/0.60  fof(f35,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f19])).
% 1.65/0.60  fof(f19,plain,(
% 1.65/0.60    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f9])).
% 1.65/0.60  fof(f9,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.65/0.60  fof(f41,plain,(
% 1.65/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.65/0.60    inference(avatar_component_clause,[],[f39])).
% 1.65/0.60  fof(f39,plain,(
% 1.65/0.60    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.65/0.60  fof(f473,plain,(
% 1.65/0.60    ( ! [X1] : (k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))) ) | ~spl3_19),
% 1.65/0.60    inference(forward_demodulation,[],[f466,f27])).
% 1.65/0.60  fof(f466,plain,(
% 1.65/0.60    ( ! [X1] : (k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(k5_xboole_0(sK0,X1),sK1)) ) | ~spl3_19),
% 1.65/0.60    inference(superposition,[],[f33,f425])).
% 1.65/0.60  fof(f425,plain,(
% 1.65/0.60    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_19),
% 1.65/0.60    inference(avatar_component_clause,[],[f423])).
% 1.65/0.60  fof(f423,plain,(
% 1.65/0.60    spl3_19 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.65/0.60  fof(f33,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f4])).
% 1.65/0.60  fof(f4,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.65/0.60  fof(f1044,plain,(
% 1.65/0.60    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | (~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13 | spl3_20)),
% 1.65/0.60    inference(superposition,[],[f463,f446])).
% 1.65/0.60  fof(f446,plain,(
% 1.65/0.60    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(sK0,sK2)) = k9_subset_1(sK0,X0,k5_xboole_0(sK0,sK2))) ) | (~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13)),
% 1.65/0.60    inference(backward_demodulation,[],[f121,f442])).
% 1.65/0.60  fof(f442,plain,(
% 1.65/0.60    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13)),
% 1.65/0.60    inference(backward_demodulation,[],[f151,f441])).
% 1.65/0.60  fof(f441,plain,(
% 1.65/0.60    sK2 = k3_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_5 | ~spl3_7 | ~spl3_13)),
% 1.65/0.60    inference(backward_demodulation,[],[f334,f440])).
% 1.65/0.60  fof(f440,plain,(
% 1.65/0.60    sK2 = k5_xboole_0(sK0,k3_subset_1(sK0,sK2)) | (~spl3_2 | ~spl3_5 | ~spl3_13)),
% 1.65/0.60    inference(backward_demodulation,[],[f129,f435])).
% 1.65/0.60  fof(f435,plain,(
% 1.65/0.60    k3_subset_1(sK0,sK2) = k3_xboole_0(sK0,k3_subset_1(sK0,sK2)) | ~spl3_13),
% 1.65/0.60    inference(superposition,[],[f60,f355])).
% 1.65/0.60  fof(f355,plain,(
% 1.65/0.60    k3_subset_1(sK0,sK2) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) | ~spl3_13),
% 1.65/0.60    inference(avatar_component_clause,[],[f353])).
% 1.65/0.60  fof(f353,plain,(
% 1.65/0.60    spl3_13 <=> k3_subset_1(sK0,sK2) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.65/0.60  fof(f60,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.60    inference(superposition,[],[f32,f26])).
% 1.65/0.60  fof(f26,plain,(
% 1.65/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.65/0.60    inference(cnf_transformation,[],[f13])).
% 1.65/0.60  fof(f13,plain,(
% 1.65/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.65/0.60    inference(rectify,[],[f2])).
% 1.65/0.60  fof(f2,axiom,(
% 1.65/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.65/0.60  fof(f32,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f5])).
% 1.65/0.60  fof(f5,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.65/0.60  fof(f129,plain,(
% 1.65/0.60    sK2 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) | (~spl3_2 | ~spl3_5)),
% 1.65/0.60    inference(forward_demodulation,[],[f120,f56])).
% 1.65/0.60  fof(f56,plain,(
% 1.65/0.60    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_2),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f46,f31])).
% 1.65/0.60  fof(f31,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.65/0.60    inference(cnf_transformation,[],[f17])).
% 1.65/0.60  fof(f17,plain,(
% 1.65/0.60    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f8])).
% 1.65/0.60  fof(f8,axiom,(
% 1.65/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.65/0.60  fof(f46,plain,(
% 1.65/0.60    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.65/0.60    inference(avatar_component_clause,[],[f44])).
% 1.65/0.60  fof(f44,plain,(
% 1.65/0.60    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.65/0.60  fof(f120,plain,(
% 1.65/0.60    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) | ~spl3_5),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f105,f36])).
% 1.65/0.60  fof(f36,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.65/0.60    inference(definition_unfolding,[],[f30,f28])).
% 1.65/0.60  fof(f30,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f16])).
% 1.65/0.60  fof(f16,plain,(
% 1.65/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f6])).
% 1.65/0.60  fof(f6,axiom,(
% 1.65/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.65/0.60  fof(f105,plain,(
% 1.65/0.60    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_5),
% 1.65/0.60    inference(avatar_component_clause,[],[f103])).
% 1.65/0.60  fof(f103,plain,(
% 1.65/0.60    spl3_5 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.65/0.60  fof(f334,plain,(
% 1.65/0.60    sK2 = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_subset_1(sK0,sK2))) | (~spl3_5 | ~spl3_7)),
% 1.65/0.60    inference(forward_demodulation,[],[f328,f139])).
% 1.65/0.60  fof(f139,plain,(
% 1.65/0.60    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_7),
% 1.65/0.60    inference(avatar_component_clause,[],[f137])).
% 1.65/0.60  fof(f137,plain,(
% 1.65/0.60    spl3_7 <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.65/0.60  fof(f328,plain,(
% 1.65/0.60    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_subset_1(sK0,sK2))) | ~spl3_5),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f105,f308])).
% 1.65/0.60  fof(f308,plain,(
% 1.65/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.65/0.60    inference(backward_demodulation,[],[f36,f296])).
% 1.65/0.60  fof(f296,plain,(
% 1.65/0.60    ( ! [X2,X1] : (k3_xboole_0(X2,k5_xboole_0(X2,X1)) = k5_xboole_0(X2,k3_xboole_0(X2,X1))) )),
% 1.65/0.60    inference(superposition,[],[f90,f27])).
% 1.65/0.60  fof(f90,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.65/0.60    inference(forward_demodulation,[],[f82,f27])).
% 1.65/0.60  fof(f82,plain,(
% 1.65/0.60    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.65/0.60    inference(superposition,[],[f33,f26])).
% 1.65/0.60  fof(f151,plain,(
% 1.65/0.60    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_9),
% 1.65/0.60    inference(avatar_component_clause,[],[f149])).
% 1.65/0.60  fof(f149,plain,(
% 1.65/0.60    spl3_9 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.65/0.60  fof(f121,plain,(
% 1.65/0.60    ( ! [X0] : (k3_xboole_0(X0,k3_subset_1(sK0,sK2)) = k9_subset_1(sK0,X0,k3_subset_1(sK0,sK2))) ) | ~spl3_5),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f105,f34])).
% 1.65/0.60  fof(f34,plain,(
% 1.65/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)) )),
% 1.65/0.60    inference(cnf_transformation,[],[f18])).
% 1.65/0.60  fof(f18,plain,(
% 1.65/0.60    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f10])).
% 1.65/0.60  fof(f10,axiom,(
% 1.65/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.65/0.60  fof(f463,plain,(
% 1.65/0.60    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | spl3_20),
% 1.65/0.60    inference(avatar_component_clause,[],[f461])).
% 1.65/0.60  fof(f461,plain,(
% 1.65/0.60    spl3_20 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.65/0.60  fof(f464,plain,(
% 1.65/0.60    ~spl3_20 | ~spl3_2 | spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13),
% 1.65/0.60    inference(avatar_split_clause,[],[f443,f353,f149,f137,f103,f49,f44,f461])).
% 1.65/0.60  fof(f49,plain,(
% 1.65/0.60    spl3_3 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.65/0.60  fof(f443,plain,(
% 1.65/0.60    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | (~spl3_2 | spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_9 | ~spl3_13)),
% 1.65/0.60    inference(backward_demodulation,[],[f51,f442])).
% 1.65/0.60  fof(f51,plain,(
% 1.65/0.60    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl3_3),
% 1.65/0.60    inference(avatar_component_clause,[],[f49])).
% 1.65/0.60  fof(f426,plain,(
% 1.65/0.60    spl3_19 | ~spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_12),
% 1.65/0.60    inference(avatar_split_clause,[],[f366,f348,f132,f73,f39,f423])).
% 1.65/0.60  fof(f73,plain,(
% 1.65/0.60    spl3_4 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.65/0.60  fof(f132,plain,(
% 1.65/0.60    spl3_6 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.65/0.60  fof(f348,plain,(
% 1.65/0.60    spl3_12 <=> k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.65/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.65/0.60  fof(f366,plain,(
% 1.65/0.60    sK1 = k3_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_4 | ~spl3_6 | ~spl3_12)),
% 1.65/0.60    inference(backward_demodulation,[],[f335,f365])).
% 1.65/0.60  fof(f365,plain,(
% 1.65/0.60    sK1 = k5_xboole_0(sK0,k3_subset_1(sK0,sK1)) | (~spl3_1 | ~spl3_4 | ~spl3_12)),
% 1.65/0.60    inference(backward_demodulation,[],[f117,f360])).
% 1.65/0.60  fof(f360,plain,(
% 1.65/0.60    k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k3_subset_1(sK0,sK1)) | ~spl3_12),
% 1.65/0.60    inference(superposition,[],[f60,f350])).
% 1.65/0.60  fof(f350,plain,(
% 1.65/0.60    k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) | ~spl3_12),
% 1.65/0.60    inference(avatar_component_clause,[],[f348])).
% 1.65/0.60  fof(f117,plain,(
% 1.65/0.60    sK1 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) | (~spl3_1 | ~spl3_4)),
% 1.65/0.60    inference(forward_demodulation,[],[f108,f55])).
% 1.65/0.60  fof(f55,plain,(
% 1.65/0.60    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_1),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f41,f31])).
% 1.65/0.60  fof(f108,plain,(
% 1.65/0.60    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) | ~spl3_4),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f75,f36])).
% 1.65/0.60  fof(f75,plain,(
% 1.65/0.60    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_4),
% 1.65/0.60    inference(avatar_component_clause,[],[f73])).
% 1.65/0.60  fof(f335,plain,(
% 1.65/0.60    sK1 = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_subset_1(sK0,sK1))) | (~spl3_4 | ~spl3_6)),
% 1.65/0.60    inference(forward_demodulation,[],[f327,f134])).
% 1.65/0.60  fof(f134,plain,(
% 1.65/0.60    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_6),
% 1.65/0.60    inference(avatar_component_clause,[],[f132])).
% 1.65/0.60  fof(f327,plain,(
% 1.65/0.60    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k3_subset_1(sK0,sK1))) | ~spl3_4),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f75,f308])).
% 1.65/0.60  fof(f356,plain,(
% 1.65/0.60    spl3_13 | ~spl3_2),
% 1.65/0.60    inference(avatar_split_clause,[],[f326,f44,f353])).
% 1.65/0.60  fof(f326,plain,(
% 1.65/0.60    k3_subset_1(sK0,sK2) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) | ~spl3_2),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f46,f308])).
% 1.65/0.60  fof(f351,plain,(
% 1.65/0.60    spl3_12 | ~spl3_1),
% 1.65/0.60    inference(avatar_split_clause,[],[f325,f39,f348])).
% 1.65/0.60  fof(f325,plain,(
% 1.65/0.60    k3_subset_1(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) | ~spl3_1),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f41,f308])).
% 1.65/0.60  fof(f152,plain,(
% 1.65/0.60    spl3_9 | ~spl3_2),
% 1.65/0.60    inference(avatar_split_clause,[],[f93,f44,f149])).
% 1.65/0.60  fof(f93,plain,(
% 1.65/0.60    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_2),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f46,f36])).
% 1.65/0.60  fof(f140,plain,(
% 1.65/0.60    spl3_7 | ~spl3_2),
% 1.65/0.60    inference(avatar_split_clause,[],[f56,f44,f137])).
% 1.65/0.60  fof(f135,plain,(
% 1.65/0.60    spl3_6 | ~spl3_1),
% 1.65/0.60    inference(avatar_split_clause,[],[f55,f39,f132])).
% 1.65/0.60  fof(f106,plain,(
% 1.65/0.60    spl3_5 | ~spl3_2),
% 1.65/0.60    inference(avatar_split_clause,[],[f54,f44,f103])).
% 1.65/0.60  fof(f54,plain,(
% 1.65/0.60    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f46,f29])).
% 1.65/0.60  fof(f29,plain,(
% 1.65/0.60    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.60    inference(cnf_transformation,[],[f15])).
% 1.65/0.60  fof(f15,plain,(
% 1.65/0.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f7])).
% 1.65/0.60  fof(f7,axiom,(
% 1.65/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.65/0.60  fof(f76,plain,(
% 1.65/0.60    spl3_4 | ~spl3_1),
% 1.65/0.60    inference(avatar_split_clause,[],[f53,f39,f73])).
% 1.65/0.60  fof(f53,plain,(
% 1.65/0.60    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.65/0.60    inference(unit_resulting_resolution,[],[f41,f29])).
% 1.65/0.60  fof(f52,plain,(
% 1.65/0.60    ~spl3_3),
% 1.65/0.60    inference(avatar_split_clause,[],[f25,f49])).
% 1.65/0.60  fof(f25,plain,(
% 1.65/0.60    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.65/0.60    inference(cnf_transformation,[],[f22])).
% 1.65/0.60  fof(f22,plain,(
% 1.65/0.60    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f21,f20])).
% 1.65/0.60  fof(f20,plain,(
% 1.65/0.60    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.65/0.60    introduced(choice_axiom,[])).
% 1.65/0.60  fof(f21,plain,(
% 1.65/0.60    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.65/0.60    introduced(choice_axiom,[])).
% 1.65/0.60  fof(f14,plain,(
% 1.65/0.60    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.60    inference(ennf_transformation,[],[f12])).
% 1.65/0.60  fof(f12,negated_conjecture,(
% 1.65/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.65/0.60    inference(negated_conjecture,[],[f11])).
% 1.65/0.60  fof(f11,conjecture,(
% 1.65/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.65/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 1.65/0.60  fof(f47,plain,(
% 1.65/0.60    spl3_2),
% 1.65/0.60    inference(avatar_split_clause,[],[f24,f44])).
% 1.65/0.60  fof(f24,plain,(
% 1.65/0.60    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.65/0.60    inference(cnf_transformation,[],[f22])).
% 1.65/0.60  fof(f42,plain,(
% 1.65/0.60    spl3_1),
% 1.65/0.60    inference(avatar_split_clause,[],[f23,f39])).
% 1.65/0.60  fof(f23,plain,(
% 1.65/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.65/0.60    inference(cnf_transformation,[],[f22])).
% 1.65/0.60  % SZS output end Proof for theBenchmark
% 1.65/0.60  % (2123)------------------------------
% 1.65/0.60  % (2123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.60  % (2123)Termination reason: Refutation
% 1.65/0.60  
% 1.65/0.60  % (2123)Memory used [KB]: 11897
% 1.65/0.60  % (2123)Time elapsed: 0.181 s
% 1.65/0.60  % (2123)------------------------------
% 1.65/0.60  % (2123)------------------------------
% 1.65/0.60  % (2107)Success in time 0.247 s
%------------------------------------------------------------------------------
