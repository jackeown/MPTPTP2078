%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 257 expanded)
%              Number of leaves         :   41 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  363 ( 672 expanded)
%              Number of equality atoms :   71 ( 150 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f599,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f142,f182,f200,f245,f265,f327,f361,f392,f410,f430,f435,f460,f463,f467,f468,f560,f594,f598])).

fof(f598,plain,(
    spl4_56 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | spl4_56 ),
    inference(unit_resulting_resolution,[],[f66,f593])).

fof(f593,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_56 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl4_56
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f594,plain,
    ( ~ spl4_56
    | spl4_4
    | ~ spl4_12
    | ~ spl4_39
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f589,f557,f353,f139,f84,f591])).

fof(f84,plain,
    ( spl4_4
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f139,plain,
    ( spl4_12
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f353,plain,
    ( spl4_39
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f557,plain,
    ( spl4_52
  <=> sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f589,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_4
    | ~ spl4_12
    | ~ spl4_39
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f588,f559])).

fof(f559,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f557])).

fof(f588,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | spl4_4
    | ~ spl4_12
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f473,f355])).

fof(f355,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f353])).

fof(f473,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK1),k8_setfam_1(sK0,sK1))
    | spl4_4
    | ~ spl4_12 ),
    inference(superposition,[],[f86,f141])).

fof(f141,plain,
    ( sK1 = sK2
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f86,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f560,plain,
    ( spl4_52
    | ~ spl4_36
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f512,f353,f324,f557])).

fof(f324,plain,
    ( spl4_36
  <=> sK0 = k8_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f512,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_36
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f326,f355])).

fof(f326,plain,
    ( sK0 = k8_setfam_1(sK0,sK1)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f324])).

fof(f468,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f467,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK1
    | r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f463,plain,
    ( ~ spl4_1
    | spl4_39
    | spl4_49 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl4_1
    | spl4_39
    | spl4_49 ),
    inference(unit_resulting_resolution,[],[f71,f354,f459,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f459,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl4_49 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl4_49
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f354,plain,
    ( k1_xboole_0 != sK1
    | spl4_39 ),
    inference(avatar_component_clause,[],[f353])).

fof(f71,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f460,plain,
    ( spl4_39
    | ~ spl4_2
    | ~ spl4_49
    | spl4_45 ),
    inference(avatar_split_clause,[],[f439,f432,f457,f74,f353])).

fof(f74,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f432,plain,
    ( spl4_45
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f439,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK1
    | spl4_45 ),
    inference(superposition,[],[f434,f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f51,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f434,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f432])).

fof(f435,plain,
    ( spl4_44
    | ~ spl4_3
    | ~ spl4_45
    | spl4_4 ),
    inference(avatar_split_clause,[],[f396,f84,f432,f79,f427])).

fof(f427,plain,
    ( spl4_44
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f79,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f396,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK2
    | spl4_4 ),
    inference(superposition,[],[f86,f222])).

fof(f430,plain,
    ( spl4_44
    | ~ spl4_3
    | ~ spl4_26
    | spl4_42 ),
    inference(avatar_split_clause,[],[f411,f407,f242,f79,f427])).

fof(f242,plain,
    ( spl4_26
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f407,plain,
    ( spl4_42
  <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f411,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK2
    | spl4_42 ),
    inference(superposition,[],[f409,f222])).

fof(f409,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl4_42 ),
    inference(avatar_component_clause,[],[f407])).

fof(f410,plain,
    ( ~ spl4_42
    | spl4_4
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f402,f324,f84,f407])).

fof(f402,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | spl4_4
    | ~ spl4_36 ),
    inference(superposition,[],[f86,f326])).

fof(f392,plain,
    ( ~ spl4_8
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | ~ spl4_8
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f118,f354,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f118,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl4_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f361,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f327,plain,
    ( ~ spl4_8
    | spl4_36
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f318,f74,f324,f116])).

fof(f318,plain,
    ( sK0 = k8_setfam_1(sK0,sK1)
    | ~ v1_xboole_0(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f153,f76])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | k8_setfam_1(X1,X0) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f65,f55])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f265,plain,(
    spl4_29 ),
    inference(avatar_split_clause,[],[f259,f262])).

fof(f262,plain,
    ( spl4_29
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f259,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f258,f110])).

fof(f110,plain,(
    ! [X2] :
      ( r2_hidden(sK3(X2),X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f258,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f240])).

fof(f240,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f63,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f59,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f60,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f63,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f54,f62])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f245,plain,
    ( ~ spl4_3
    | spl4_26
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f206,f197,f242,f79])).

fof(f197,plain,
    ( spl4_20
  <=> r1_tarski(k6_setfam_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f206,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_20 ),
    inference(superposition,[],[f199,f51])).

fof(f199,plain,
    ( r1_tarski(k6_setfam_1(sK0,sK2),sK0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f200,plain,
    ( spl4_20
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f187,f79,f197])).

fof(f187,plain,
    ( r1_tarski(k6_setfam_1(sK0,sK2),sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f176,f81])).

fof(f81,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f176,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
      | r1_tarski(k6_setfam_1(X3,X2),X3) ) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

% (4291)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_setfam_1)).

fof(f182,plain,
    ( spl4_8
    | ~ spl4_18
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f171,f69,f179,f116])).

fof(f179,plain,
    ( spl4_18
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f171,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f105,f71])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f53,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f142,plain,
    ( ~ spl4_11
    | spl4_12
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f130,f69,f139,f135])).

fof(f135,plain,
    ( spl4_11
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f130,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f48,f71])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f82,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f39,f79])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f38,f74])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f40,f69])).

fof(f40,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:13:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (4285)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.51  % (4298)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (4277)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (4290)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (4281)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (4285)Refutation not found, incomplete strategy% (4285)------------------------------
% 0.22/0.52  % (4285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4295)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (4286)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (4285)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4285)Memory used [KB]: 10746
% 0.22/0.52  % (4285)Time elapsed: 0.103 s
% 0.22/0.52  % (4285)------------------------------
% 0.22/0.52  % (4285)------------------------------
% 0.22/0.53  % (4275)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (4276)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (4282)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (4276)Refutation not found, incomplete strategy% (4276)------------------------------
% 0.22/0.53  % (4276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4276)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4276)Memory used [KB]: 1791
% 0.22/0.53  % (4276)Time elapsed: 0.114 s
% 0.22/0.53  % (4276)------------------------------
% 0.22/0.53  % (4276)------------------------------
% 0.22/0.53  % (4303)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.53  % (4304)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (4303)Refutation not found, incomplete strategy% (4303)------------------------------
% 0.22/0.53  % (4303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (4303)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (4303)Memory used [KB]: 10746
% 0.22/0.53  % (4303)Time elapsed: 0.103 s
% 0.22/0.53  % (4303)------------------------------
% 0.22/0.53  % (4303)------------------------------
% 0.22/0.53  % (4296)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (4279)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (4280)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (4289)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (4292)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (4298)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f599,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f142,f182,f200,f245,f265,f327,f361,f392,f410,f430,f435,f460,f463,f467,f468,f560,f594,f598])).
% 0.22/0.54  fof(f598,plain,(
% 0.22/0.54    spl4_56),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f595])).
% 0.22/0.54  fof(f595,plain,(
% 0.22/0.54    $false | spl4_56),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f66,f593])).
% 0.22/0.54  fof(f593,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK0) | spl4_56),
% 0.22/0.54    inference(avatar_component_clause,[],[f591])).
% 0.22/0.54  fof(f591,plain,(
% 0.22/0.54    spl4_56 <=> r1_tarski(sK0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f594,plain,(
% 0.22/0.54    ~spl4_56 | spl4_4 | ~spl4_12 | ~spl4_39 | ~spl4_52),
% 0.22/0.54    inference(avatar_split_clause,[],[f589,f557,f353,f139,f84,f591])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl4_4 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    spl4_12 <=> sK1 = sK2),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.54  fof(f353,plain,(
% 0.22/0.54    spl4_39 <=> k1_xboole_0 = sK1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.22/0.54  fof(f557,plain,(
% 0.22/0.54    spl4_52 <=> sK0 = k8_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.22/0.54  fof(f589,plain,(
% 0.22/0.54    ~r1_tarski(sK0,sK0) | (spl4_4 | ~spl4_12 | ~spl4_39 | ~spl4_52)),
% 0.22/0.54    inference(forward_demodulation,[],[f588,f559])).
% 0.22/0.54  fof(f559,plain,(
% 0.22/0.54    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl4_52),
% 0.22/0.54    inference(avatar_component_clause,[],[f557])).
% 0.22/0.54  fof(f588,plain,(
% 0.22/0.54    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | (spl4_4 | ~spl4_12 | ~spl4_39)),
% 0.22/0.54    inference(forward_demodulation,[],[f473,f355])).
% 0.22/0.54  fof(f355,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | ~spl4_39),
% 0.22/0.54    inference(avatar_component_clause,[],[f353])).
% 0.22/0.54  fof(f473,plain,(
% 0.22/0.54    ~r1_tarski(k8_setfam_1(sK0,sK1),k8_setfam_1(sK0,sK1)) | (spl4_4 | ~spl4_12)),
% 0.22/0.54    inference(superposition,[],[f86,f141])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    sK1 = sK2 | ~spl4_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f139])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl4_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f84])).
% 0.22/0.54  fof(f560,plain,(
% 0.22/0.54    spl4_52 | ~spl4_36 | ~spl4_39),
% 0.22/0.54    inference(avatar_split_clause,[],[f512,f353,f324,f557])).
% 0.22/0.54  fof(f324,plain,(
% 0.22/0.54    spl4_36 <=> sK0 = k8_setfam_1(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.54  fof(f512,plain,(
% 0.22/0.54    sK0 = k8_setfam_1(sK0,k1_xboole_0) | (~spl4_36 | ~spl4_39)),
% 0.22/0.54    inference(forward_demodulation,[],[f326,f355])).
% 0.22/0.54  fof(f326,plain,(
% 0.22/0.54    sK0 = k8_setfam_1(sK0,sK1) | ~spl4_36),
% 0.22/0.54    inference(avatar_component_clause,[],[f324])).
% 0.22/0.54  fof(f468,plain,(
% 0.22/0.54    k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f467,plain,(
% 0.22/0.54    k1_xboole_0 != sK2 | k1_xboole_0 != sK1 | r1_tarski(sK2,sK1) | ~r1_tarski(sK1,sK2)),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f463,plain,(
% 0.22/0.54    ~spl4_1 | spl4_39 | spl4_49),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f461])).
% 0.22/0.54  fof(f461,plain,(
% 0.22/0.54    $false | (~spl4_1 | spl4_39 | spl4_49)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f71,f354,f459,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.22/0.54  fof(f459,plain,(
% 0.22/0.54    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl4_49),
% 0.22/0.54    inference(avatar_component_clause,[],[f457])).
% 0.22/0.54  fof(f457,plain,(
% 0.22/0.54    spl4_49 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | spl4_39),
% 0.22/0.54    inference(avatar_component_clause,[],[f353])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | ~spl4_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    spl4_1 <=> r1_tarski(sK1,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.54  fof(f460,plain,(
% 0.22/0.54    spl4_39 | ~spl4_2 | ~spl4_49 | spl4_45),
% 0.22/0.54    inference(avatar_split_clause,[],[f439,f432,f457,f74,f353])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.54  fof(f432,plain,(
% 0.22/0.54    spl4_45 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.22/0.54  fof(f439,plain,(
% 0.22/0.54    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = sK1 | spl4_45),
% 0.22/0.54    inference(superposition,[],[f434,f222])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f217])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.54    inference(superposition,[],[f51,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.22/0.54  fof(f434,plain,(
% 0.22/0.54    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | spl4_45),
% 0.22/0.54    inference(avatar_component_clause,[],[f432])).
% 0.22/0.54  fof(f435,plain,(
% 0.22/0.54    spl4_44 | ~spl4_3 | ~spl4_45 | spl4_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f396,f84,f432,f79,f427])).
% 0.22/0.54  fof(f427,plain,(
% 0.22/0.54    spl4_44 <=> k1_xboole_0 = sK2),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.54  fof(f396,plain,(
% 0.22/0.54    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = sK2 | spl4_4),
% 0.22/0.54    inference(superposition,[],[f86,f222])).
% 0.22/0.54  fof(f430,plain,(
% 0.22/0.54    spl4_44 | ~spl4_3 | ~spl4_26 | spl4_42),
% 0.22/0.54    inference(avatar_split_clause,[],[f411,f407,f242,f79,f427])).
% 0.22/0.54  fof(f242,plain,(
% 0.22/0.54    spl4_26 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.54  fof(f407,plain,(
% 0.22/0.54    spl4_42 <=> r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.22/0.54  fof(f411,plain,(
% 0.22/0.54    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = sK2 | spl4_42),
% 0.22/0.54    inference(superposition,[],[f409,f222])).
% 0.22/0.54  fof(f409,plain,(
% 0.22/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | spl4_42),
% 0.22/0.54    inference(avatar_component_clause,[],[f407])).
% 0.22/0.54  fof(f410,plain,(
% 0.22/0.54    ~spl4_42 | spl4_4 | ~spl4_36),
% 0.22/0.54    inference(avatar_split_clause,[],[f402,f324,f84,f407])).
% 0.22/0.54  fof(f402,plain,(
% 0.22/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | (spl4_4 | ~spl4_36)),
% 0.22/0.54    inference(superposition,[],[f86,f326])).
% 0.22/0.54  fof(f392,plain,(
% 0.22/0.54    ~spl4_8 | spl4_39),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f389])).
% 0.22/0.54  fof(f389,plain,(
% 0.22/0.54    $false | (~spl4_8 | spl4_39)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f118,f354,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    v1_xboole_0(sK1) | ~spl4_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f116])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    spl4_8 <=> v1_xboole_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.54  fof(f361,plain,(
% 0.22/0.54    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f327,plain,(
% 0.22/0.54    ~spl4_8 | spl4_36 | ~spl4_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f318,f74,f324,f116])).
% 0.22/0.54  fof(f318,plain,(
% 0.22/0.54    sK0 = k8_setfam_1(sK0,sK1) | ~v1_xboole_0(sK1) | ~spl4_2),
% 0.22/0.54    inference(resolution,[],[f153,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f74])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | k8_setfam_1(X1,X0) = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(superposition,[],[f65,f55])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(equality_resolution,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    spl4_29),
% 0.22/0.54    inference(avatar_split_clause,[],[f259,f262])).
% 0.22/0.54  fof(f262,plain,(
% 0.22/0.54    spl4_29 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(resolution,[],[f258,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X2] : (r2_hidden(sK3(X2),X2) | v1_xboole_0(X2)) )),
% 0.22/0.54    inference(resolution,[],[f57,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK3(X0),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0] : m1_subset_1(sK3(X0),X0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK3(X0),X0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.54  fof(f258,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f240])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(superposition,[],[f63,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0))))) = X1 | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f58,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f59,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f60,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_tarski(X0)))))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f54,f62])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.54  fof(f245,plain,(
% 0.22/0.54    ~spl4_3 | spl4_26 | ~spl4_20),
% 0.22/0.54    inference(avatar_split_clause,[],[f206,f197,f242,f79])).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    spl4_20 <=> r1_tarski(k6_setfam_1(sK0,sK2),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_20),
% 0.22/0.54    inference(superposition,[],[f199,f51])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    r1_tarski(k6_setfam_1(sK0,sK2),sK0) | ~spl4_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f197])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    spl4_20 | ~spl4_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f187,f79,f197])).
% 0.22/0.54  fof(f187,plain,(
% 0.22/0.54    r1_tarski(k6_setfam_1(sK0,sK2),sK0) | ~spl4_3),
% 0.22/0.54    inference(resolution,[],[f176,f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f79])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) | r1_tarski(k6_setfam_1(X3,X2),X3)) )),
% 0.22/0.54    inference(resolution,[],[f50,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  % (4291)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_setfam_1)).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    spl4_8 | ~spl4_18 | ~spl4_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f171,f69,f179,f116])).
% 0.22/0.54  fof(f179,plain,(
% 0.22/0.54    spl4_18 <=> v1_xboole_0(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ~v1_xboole_0(sK2) | v1_xboole_0(sK1) | ~spl4_1),
% 0.22/0.54    inference(resolution,[],[f105,f71])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(resolution,[],[f53,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ~spl4_11 | spl4_12 | ~spl4_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f130,f69,f139,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    spl4_11 <=> r1_tarski(sK2,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    sK1 = sK2 | ~r1_tarski(sK2,sK1) | ~spl4_1),
% 0.22/0.54    inference(resolution,[],[f48,f71])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ~spl4_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f41,f84])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f31,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f16])).
% 0.22/0.54  fof(f16,conjecture,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    spl4_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f39,f79])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    spl4_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f38,f74])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    spl4_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f40,f69])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (4298)------------------------------
% 0.22/0.54  % (4298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4298)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (4298)Memory used [KB]: 11129
% 0.22/0.54  % (4298)Time elapsed: 0.078 s
% 0.22/0.54  % (4298)------------------------------
% 0.22/0.54  % (4298)------------------------------
% 0.22/0.54  % (4297)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (4289)Refutation not found, incomplete strategy% (4289)------------------------------
% 0.22/0.54  % (4289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (4289)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (4289)Memory used [KB]: 1791
% 0.22/0.54  % (4289)Time elapsed: 0.135 s
% 0.22/0.54  % (4289)------------------------------
% 0.22/0.54  % (4289)------------------------------
% 0.22/0.54  % (4274)Success in time 0.173 s
%------------------------------------------------------------------------------
