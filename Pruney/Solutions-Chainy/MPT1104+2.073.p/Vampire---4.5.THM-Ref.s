%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 192 expanded)
%              Number of leaves         :   26 (  84 expanded)
%              Depth                    :    7
%              Number of atoms          :  240 ( 462 expanded)
%              Number of equality atoms :   67 ( 164 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f105,f110,f134,f141,f146,f157,f165,f174,f195,f226,f255,f258])).

fof(f258,plain,
    ( ~ spl3_2
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl3_2
    | spl3_20 ),
    inference(unit_resulting_resolution,[],[f71,f254,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f254,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl3_20
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f71,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f255,plain,
    ( ~ spl3_20
    | spl3_18
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f244,f192,f171,f223,f252])).

fof(f223,plain,
    ( spl3_18
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f171,plain,
    ( spl3_14
  <=> k2_struct_0(sK0) = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f192,plain,
    ( spl3_15
  <=> k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f244,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ r1_xboole_0(sK2,sK1)
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f180,f194])).

fof(f194,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f192])).

fof(f180,plain,
    ( sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ r1_xboole_0(sK2,sK1)
    | ~ spl3_14 ),
    inference(superposition,[],[f46,f173])).

fof(f173,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK2,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f171])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f226,plain,
    ( ~ spl3_18
    | spl3_8
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f216,f192,f102,f223])).

fof(f102,plain,
    ( spl3_8
  <=> sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f216,plain,
    ( sK2 != k4_xboole_0(sK2,sK1)
    | spl3_8
    | ~ spl3_15 ),
    inference(superposition,[],[f104,f194])).

fof(f104,plain,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f195,plain,
    ( spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f179,f171,f192])).

fof(f179,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1)
    | ~ spl3_14 ),
    inference(superposition,[],[f44,f173])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f174,plain,
    ( spl3_14
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f169,f162,f143,f171])).

fof(f143,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f162,plain,
    ( spl3_13
  <=> sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f169,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK2,sK1)
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f167,f145])).

fof(f145,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f167,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(superposition,[],[f43,f164])).

fof(f164,plain,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f162])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f165,plain,
    ( spl3_13
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f158,f154,f131,f162])).

fof(f131,plain,
    ( spl3_10
  <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f154,plain,
    ( spl3_12
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f158,plain,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f133,f156])).

fof(f156,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f133,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_struct_0(sK0),sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f157,plain,
    ( ~ spl3_2
    | spl3_12
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f152,f131,f107,f154,f69])).

fof(f107,plain,
    ( spl3_9
  <=> k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f152,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f112,f133])).

fof(f112,plain,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_9 ),
    inference(superposition,[],[f46,f109])).

fof(f109,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f146,plain,
    ( spl3_11
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f140,f131,f107,f143])).

fof(f140,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f139,f109])).

fof(f139,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f138,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f138,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k2_struct_0(sK0))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f136,f43])).

fof(f136,plain,
    ( k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_10 ),
    inference(superposition,[],[f43,f133])).

fof(f141,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f95,f84,f98,f79,f74])).

fof(f74,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k9_setfam_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f98,plain,
    ( spl3_7
  <=> m1_subset_1(k2_struct_0(sK0),k9_setfam_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f84,plain,
    ( spl3_5
  <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f95,plain,
    ( m1_subset_1(k2_struct_0(sK0),k9_setfam_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f60,f86])).

fof(f86,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f37,f37,f37])).

fof(f37,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f134,plain,
    ( spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f111,f107,f131])).

fof(f111,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_struct_0(sK0),sK2)
    | ~ spl3_9 ),
    inference(superposition,[],[f44,f109])).

fof(f110,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f93,f84,f107,f79,f74])).

fof(f93,plain,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f86,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f37,f37])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f105,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f96,f89,f102,f98])).

fof(f89,plain,
    ( spl3_6
  <=> sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f96,plain,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k9_setfam_1(u1_struct_0(sK0)))
    | spl3_6 ),
    inference(superposition,[],[f91,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f37])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f91,plain,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f92,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
              & r1_xboole_0(X1,X2)
              & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).

fof(f87,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f84])).

fof(f31,plain,(
    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f55,f79])).

fof(f55,plain,(
    m1_subset_1(sK2,k9_setfam_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f54,f74])).

fof(f54,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:37:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (32600)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (32604)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (32596)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (32592)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (32588)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (32608)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (32604)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f259,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f105,f110,f134,f141,f146,f157,f165,f174,f195,f226,f255,f258])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    ~spl3_2 | spl3_20),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f256])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    $false | (~spl3_2 | spl3_20)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f71,f254,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    ~r1_xboole_0(sK2,sK1) | spl3_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f252])).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    spl3_20 <=> r1_xboole_0(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    ~spl3_20 | spl3_18 | ~spl3_14 | ~spl3_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f244,f192,f171,f223,f252])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    spl3_18 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    spl3_14 <=> k2_struct_0(sK0) = k2_xboole_0(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    spl3_15 <=> k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    sK2 = k4_xboole_0(sK2,sK1) | ~r1_xboole_0(sK2,sK1) | (~spl3_14 | ~spl3_15)),
% 0.22/0.53    inference(forward_demodulation,[],[f180,f194])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1) | ~spl3_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f192])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) | ~r1_xboole_0(sK2,sK1) | ~spl3_14),
% 0.22/0.53    inference(superposition,[],[f46,f173])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_xboole_0(sK2,sK1) | ~spl3_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f171])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    ~spl3_18 | spl3_8 | ~spl3_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f216,f192,f102,f223])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    spl3_8 <=> sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    sK2 != k4_xboole_0(sK2,sK1) | (spl3_8 | ~spl3_15)),
% 0.22/0.53    inference(superposition,[],[f104,f194])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    sK2 != k4_xboole_0(k2_struct_0(sK0),sK1) | spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f102])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    spl3_15 | ~spl3_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f179,f171,f192])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1) | ~spl3_14),
% 0.22/0.53    inference(superposition,[],[f44,f173])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    spl3_14 | ~spl3_11 | ~spl3_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f169,f162,f143,f171])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    spl3_11 <=> k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    spl3_13 <=> sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_xboole_0(sK2,sK1) | (~spl3_11 | ~spl3_13)),
% 0.22/0.53    inference(forward_demodulation,[],[f167,f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0)) | ~spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f143])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.22/0.53    inference(superposition,[],[f43,f164])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) | ~spl3_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f162])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    spl3_13 | ~spl3_10 | ~spl3_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f158,f154,f131,f162])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    spl3_10 <=> k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_struct_0(sK0),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    spl3_12 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) | (~spl3_10 | ~spl3_12)),
% 0.22/0.53    inference(backward_demodulation,[],[f133,f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f154])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_struct_0(sK0),sK2) | ~spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f131])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ~spl3_2 | spl3_12 | ~spl3_9 | ~spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f152,f131,f107,f154,f69])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl3_9 <=> k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    sK1 = k4_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK2) | (~spl3_9 | ~spl3_10)),
% 0.22/0.53    inference(forward_demodulation,[],[f112,f133])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) | ~r1_xboole_0(sK1,sK2) | ~spl3_9),
% 0.22/0.53    inference(superposition,[],[f46,f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) | ~spl3_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f107])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    spl3_11 | ~spl3_9 | ~spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f140,f131,f107,f143])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0)) | (~spl3_9 | ~spl3_10)),
% 0.22/0.53    inference(forward_demodulation,[],[f139,f109])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,k2_struct_0(sK0)) | ~spl3_10),
% 0.22/0.53    inference(forward_demodulation,[],[f138,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k2_struct_0(sK0)) | ~spl3_10),
% 0.22/0.53    inference(forward_demodulation,[],[f136,f43])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_10),
% 0.22/0.53    inference(superposition,[],[f43,f133])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ~spl3_3 | ~spl3_4 | spl3_7 | ~spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f95,f84,f98,f79,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl3_3 <=> m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl3_4 <=> m1_subset_1(sK2,k9_setfam_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    spl3_7 <=> m1_subset_1(k2_struct_0(sK0),k9_setfam_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    spl3_5 <=> k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    m1_subset_1(k2_struct_0(sK0),k9_setfam_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k9_setfam_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.22/0.53    inference(superposition,[],[f60,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f84])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f52,f37,f37,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    spl3_10 | ~spl3_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f111,f107,f131])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    k4_xboole_0(sK1,sK2) = k4_xboole_0(k2_struct_0(sK0),sK2) | ~spl3_9),
% 0.22/0.53    inference(superposition,[],[f44,f109])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ~spl3_3 | ~spl3_4 | spl3_9 | ~spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f93,f84,f107,f79,f74])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) | ~m1_subset_1(sK2,k9_setfam_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.22/0.53    inference(superposition,[],[f86,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f53,f37,f37])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    ~spl3_7 | ~spl3_8 | spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f96,f89,f102,f98])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl3_6 <=> sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    sK2 != k4_xboole_0(k2_struct_0(sK0),sK1) | ~m1_subset_1(k2_struct_0(sK0),k9_setfam_1(u1_struct_0(sK0))) | spl3_6),
% 0.22/0.53    inference(superposition,[],[f91,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k9_setfam_1(X0))) )),
% 0.22/0.53    inference(definition_unfolding,[],[f50,f37])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | spl3_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ~spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f89])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 0.22/0.53    inference(negated_conjecture,[],[f16])).
% 0.22/0.53  fof(f16,conjecture,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_pre_topc)).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f84])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f79])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    m1_subset_1(sK2,k9_setfam_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(definition_unfolding,[],[f30,f37])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f54,f74])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(definition_unfolding,[],[f34,f37])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f69])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    r1_xboole_0(sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (32604)------------------------------
% 0.22/0.53  % (32604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32604)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (32604)Memory used [KB]: 10874
% 0.22/0.53  % (32604)Time elapsed: 0.073 s
% 0.22/0.53  % (32604)------------------------------
% 0.22/0.53  % (32604)------------------------------
% 0.22/0.54  % (32586)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (32593)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (32582)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (32603)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (32585)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (32577)Success in time 0.178 s
%------------------------------------------------------------------------------
