%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 213 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :    8
%              Number of atoms          :  276 ( 575 expanded)
%              Number of equality atoms :   50 ( 123 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f67,f134,f141,f155,f164,f168,f189,f229,f282,f283,f286,f396,f441,f483,f488,f491])).

fof(f491,plain,
    ( ~ spl3_36
    | spl3_61 ),
    inference(avatar_split_clause,[],[f489,f486,f277])).

fof(f277,plain,
    ( spl3_36
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f486,plain,
    ( spl3_61
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f489,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_61 ),
    inference(resolution,[],[f487,f83])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f34,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f487,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_61 ),
    inference(avatar_component_clause,[],[f486])).

fof(f488,plain,
    ( ~ spl3_61
    | spl3_60 ),
    inference(avatar_split_clause,[],[f484,f481,f486])).

fof(f481,plain,
    ( spl3_60
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f484,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_60 ),
    inference(resolution,[],[f482,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f482,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_60 ),
    inference(avatar_component_clause,[],[f481])).

fof(f483,plain,
    ( ~ spl3_36
    | ~ spl3_60
    | spl3_57 ),
    inference(avatar_split_clause,[],[f479,f434,f481,f277])).

fof(f434,plain,
    ( spl3_57
  <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f479,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_57 ),
    inference(superposition,[],[f435,f39])).

fof(f435,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_57 ),
    inference(avatar_component_clause,[],[f434])).

fof(f441,plain,
    ( ~ spl3_57
    | spl3_1
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f440,f139,f132,f41,f434])).

fof(f41,plain,
    ( spl3_1
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f132,plain,
    ( spl3_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f139,plain,
    ( spl3_16
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f440,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f178,f133])).

fof(f133,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f178,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_16 ),
    inference(superposition,[],[f42,f140])).

fof(f140,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f42,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f396,plain,
    ( spl3_16
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f394,f204,f139])).

fof(f204,plain,
    ( spl3_28
  <=> k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f394,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_28 ),
    inference(superposition,[],[f30,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f204])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f286,plain,
    ( ~ spl3_20
    | spl3_37 ),
    inference(avatar_split_clause,[],[f284,f280,f162])).

fof(f162,plain,
    ( spl3_20
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f280,plain,
    ( spl3_37
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f284,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl3_37 ),
    inference(resolution,[],[f281,f37])).

fof(f281,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_37 ),
    inference(avatar_component_clause,[],[f280])).

fof(f283,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f282,plain,
    ( ~ spl3_36
    | ~ spl3_37
    | spl3_24 ),
    inference(avatar_split_clause,[],[f275,f187,f280,f277])).

fof(f187,plain,
    ( spl3_24
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f275,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_24 ),
    inference(superposition,[],[f188,f39])).

fof(f188,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f187])).

fof(f229,plain,
    ( spl3_28
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f213,f132,f65,f204])).

fof(f65,plain,
    ( spl3_6
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f213,plain,
    ( k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(superposition,[],[f66,f133])).

fof(f66,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f189,plain,
    ( ~ spl3_24
    | spl3_1
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f185,f139,f129,f41,f187])).

fof(f129,plain,
    ( spl3_13
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f185,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | spl3_1
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f178,f130])).

fof(f130,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f168,plain,
    ( ~ spl3_2
    | spl3_16
    | spl3_18 ),
    inference(avatar_split_clause,[],[f165,f153,f139,f45])).

fof(f45,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f153,plain,
    ( spl3_18
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f165,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | spl3_18 ),
    inference(resolution,[],[f154,f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f154,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f164,plain,
    ( ~ spl3_3
    | spl3_20
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f145,f129,f162,f49])).

fof(f49,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f145,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_13 ),
    inference(superposition,[],[f34,f130])).

fof(f155,plain,
    ( ~ spl3_18
    | spl3_1
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f151,f136,f129,f41,f153])).

fof(f136,plain,
    ( spl3_15
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f151,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_1
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f143,f137])).

fof(f137,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f143,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_1
    | ~ spl3_13 ),
    inference(superposition,[],[f42,f130])).

fof(f141,plain,
    ( spl3_15
    | spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f123,f53,f139,f136])).

fof(f53,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f94,f54])).

fof(f54,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f94,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f35,f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f134,plain,
    ( spl3_13
    | spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f122,f49,f132,f129])).

fof(f122,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f94,f50])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f67,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f62,f45,f65])).

fof(f62,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

% (24326)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f55,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f53])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f51,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f45])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f28,f41])).

fof(f28,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (24321)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (24318)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (24327)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (24319)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (24329)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (24313)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (24319)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f492,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f67,f134,f141,f155,f164,f168,f189,f229,f282,f283,f286,f396,f441,f483,f488,f491])).
% 0.21/0.48  fof(f491,plain,(
% 0.21/0.48    ~spl3_36 | spl3_61),
% 0.21/0.48    inference(avatar_split_clause,[],[f489,f486,f277])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    spl3_36 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.48  fof(f486,plain,(
% 0.21/0.48    spl3_61 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.21/0.48  fof(f489,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_61),
% 0.21/0.48    inference(resolution,[],[f487,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(superposition,[],[f34,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.21/0.48  fof(f487,plain,(
% 0.21/0.48    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_61),
% 0.21/0.48    inference(avatar_component_clause,[],[f486])).
% 0.21/0.48  fof(f488,plain,(
% 0.21/0.48    ~spl3_61 | spl3_60),
% 0.21/0.48    inference(avatar_split_clause,[],[f484,f481,f486])).
% 0.21/0.48  fof(f481,plain,(
% 0.21/0.48    spl3_60 <=> r1_tarski(sK0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.21/0.48  fof(f484,plain,(
% 0.21/0.48    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_60),
% 0.21/0.48    inference(resolution,[],[f482,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f482,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK0) | spl3_60),
% 0.21/0.48    inference(avatar_component_clause,[],[f481])).
% 0.21/0.48  fof(f483,plain,(
% 0.21/0.48    ~spl3_36 | ~spl3_60 | spl3_57),
% 0.21/0.48    inference(avatar_split_clause,[],[f479,f434,f481,f277])).
% 0.21/0.48  fof(f434,plain,(
% 0.21/0.48    spl3_57 <=> r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.48  fof(f479,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_57),
% 0.21/0.48    inference(superposition,[],[f435,f39])).
% 0.21/0.48  fof(f435,plain,(
% 0.21/0.48    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | spl3_57),
% 0.21/0.48    inference(avatar_component_clause,[],[f434])).
% 0.21/0.48  fof(f441,plain,(
% 0.21/0.48    ~spl3_57 | spl3_1 | ~spl3_14 | ~spl3_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f440,f139,f132,f41,f434])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl3_1 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl3_14 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl3_16 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f440,plain,(
% 0.21/0.48    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_14 | ~spl3_16)),
% 0.21/0.48    inference(forward_demodulation,[],[f178,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl3_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f132])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_16)),
% 0.21/0.48    inference(superposition,[],[f42,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f139])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    spl3_16 | ~spl3_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f394,f204,f139])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    spl3_28 <=> k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.48  fof(f394,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl3_28),
% 0.21/0.48    inference(superposition,[],[f30,f205])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0) | ~spl3_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f204])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.48  fof(f286,plain,(
% 0.21/0.48    ~spl3_20 | spl3_37),
% 0.21/0.48    inference(avatar_split_clause,[],[f284,f280,f162])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    spl3_20 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    spl3_37 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | spl3_37),
% 0.21/0.48    inference(resolution,[],[f281,f37])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl3_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f280])).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    ~spl3_36 | ~spl3_37 | spl3_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f275,f187,f280,f277])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    spl3_24 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_24),
% 0.21/0.48    inference(superposition,[],[f188,f39])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | spl3_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f187])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    spl3_28 | ~spl3_6 | ~spl3_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f213,f132,f65,f204])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl3_6 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    k1_xboole_0 = k2_xboole_0(sK1,k1_xboole_0) | (~spl3_6 | ~spl3_14)),
% 0.21/0.48    inference(superposition,[],[f66,f133])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ~spl3_24 | spl3_1 | ~spl3_13 | ~spl3_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f185,f139,f129,f41,f187])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl3_13 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (spl3_1 | ~spl3_13 | ~spl3_16)),
% 0.21/0.48    inference(forward_demodulation,[],[f178,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ~spl3_2 | spl3_16 | spl3_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f165,f153,f139,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    spl3_18 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | spl3_18),
% 0.21/0.48    inference(resolution,[],[f154,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f153])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ~spl3_3 | spl3_20 | ~spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f145,f129,f162,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_13),
% 0.21/0.48    inference(superposition,[],[f34,f130])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~spl3_18 | spl3_1 | ~spl3_13 | ~spl3_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f151,f136,f129,f41,f153])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl3_15 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl3_1 | ~spl3_13 | ~spl3_15)),
% 0.21/0.48    inference(forward_demodulation,[],[f143,f137])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f136])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl3_1 | ~spl3_13)),
% 0.21/0.48    inference(superposition,[],[f42,f130])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl3_15 | spl3_16 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f123,f53,f139,f136])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f94,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.21/0.48    inference(superposition,[],[f35,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl3_13 | spl3_14 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f49,f132,f129])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_3),
% 0.21/0.48    inference(resolution,[],[f94,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_6 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f62,f45,f65])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f31,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  % (24326)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f53])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f22,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f49])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f45])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f41])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (24319)------------------------------
% 0.21/0.48  % (24319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24319)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (24319)Memory used [KB]: 10874
% 0.21/0.48  % (24319)Time elapsed: 0.017 s
% 0.21/0.48  % (24319)------------------------------
% 0.21/0.48  % (24319)------------------------------
% 0.21/0.48  % (24314)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (24326)Refutation not found, incomplete strategy% (24326)------------------------------
% 0.21/0.48  % (24326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24326)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (24326)Memory used [KB]: 1663
% 0.21/0.48  % (24326)Time elapsed: 0.074 s
% 0.21/0.48  % (24326)------------------------------
% 0.21/0.48  % (24326)------------------------------
% 0.21/0.48  % (24312)Success in time 0.13 s
%------------------------------------------------------------------------------
