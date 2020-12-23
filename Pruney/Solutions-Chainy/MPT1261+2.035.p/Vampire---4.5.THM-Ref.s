%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:53 EST 2020

% Result     : Theorem 5.60s
% Output     : Refutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 999 expanded)
%              Number of leaves         :   40 ( 339 expanded)
%              Depth                    :   17
%              Number of atoms          :  500 (1797 expanded)
%              Number of equality atoms :  126 ( 770 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8111,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f116,f121,f147,f217,f260,f422,f2737,f2742,f2753,f3349,f3376,f6657,f7652,f8006,f8037])).

fof(f8037,plain,
    ( ~ spl2_8
    | ~ spl2_43
    | spl2_55 ),
    inference(avatar_contradiction_clause,[],[f8036])).

fof(f8036,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_43
    | spl2_55 ),
    inference(subsumption_resolution,[],[f3337,f6681])).

fof(f6681,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_8
    | ~ spl2_43 ),
    inference(backward_demodulation,[],[f2988,f252])).

fof(f252,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl2_8
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f2988,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_43 ),
    inference(superposition,[],[f210,f2736])).

fof(f2736,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f2734])).

fof(f2734,plain,
    ( spl2_43
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f210,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(forward_demodulation,[],[f204,f98])).

fof(f98,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(definition_unfolding,[],[f78,f75,f93,f75])).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f77,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f204,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(unit_resulting_resolution,[],[f136,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)
      | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f90,f75,f93])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f136,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f135,f105])).

fof(f105,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f95,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f95,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f66,f93])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f135,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f96,f94])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f72,f93])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3337,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_55 ),
    inference(avatar_component_clause,[],[f3336])).

fof(f3336,plain,
    ( spl2_55
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f8006,plain,
    ( ~ spl2_3
    | ~ spl2_7
    | ~ spl2_43
    | ~ spl2_46
    | ~ spl2_56
    | ~ spl2_85 ),
    inference(avatar_contradiction_clause,[],[f8005])).

fof(f8005,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_43
    | ~ spl2_46
    | ~ spl2_56
    | ~ spl2_85 ),
    inference(subsumption_resolution,[],[f8004,f7915])).

fof(f7915,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_7
    | ~ spl2_43
    | ~ spl2_46
    | ~ spl2_56
    | ~ spl2_85 ),
    inference(backward_demodulation,[],[f216,f7914])).

fof(f7914,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_43
    | ~ spl2_46
    | ~ spl2_56
    | ~ spl2_85 ),
    inference(forward_demodulation,[],[f3342,f7911])).

fof(f7911,plain,
    ( sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_46
    | ~ spl2_56
    | ~ spl2_85 ),
    inference(forward_demodulation,[],[f7772,f7891])).

fof(f7891,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_46
    | ~ spl2_85 ),
    inference(forward_demodulation,[],[f7797,f7883])).

fof(f7883,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_46
    | ~ spl2_85 ),
    inference(forward_demodulation,[],[f7803,f2752])).

fof(f2752,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f2750])).

fof(f2750,plain,
    ( spl2_46
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f7803,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_85 ),
    inference(resolution,[],[f6656,f455])).

fof(f455,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f99,f427])).

fof(f427,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f180,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f88,f93])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f180,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f136,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f80,f93])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f6656,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_85 ),
    inference(avatar_component_clause,[],[f6654])).

fof(f6654,plain,
    ( spl2_85
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).

fof(f7797,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_85 ),
    inference(resolution,[],[f6656,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f82,f64])).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f7772,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_56
    | ~ spl2_85 ),
    inference(unit_resulting_resolution,[],[f3375,f6656,f242])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f104,f87])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f92,f75])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f3375,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f3373])).

fof(f3373,plain,
    ( spl2_56
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f3342,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_43
    | ~ spl2_46 ),
    inference(forward_demodulation,[],[f3341,f2736])).

fof(f3341,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_46 ),
    inference(forward_demodulation,[],[f3014,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f3014,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_46 ),
    inference(superposition,[],[f454,f2752])).

fof(f454,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k7_subset_1(X1,X1,X0))) ),
    inference(backward_demodulation,[],[f98,f427])).

fof(f216,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl2_7
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f8004,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_46
    | ~ spl2_85 ),
    inference(subsumption_resolution,[],[f6670,f7896])).

fof(f7896,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_46
    | ~ spl2_85 ),
    inference(backward_demodulation,[],[f7884,f7892])).

fof(f7892,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_46
    | ~ spl2_85 ),
    inference(forward_demodulation,[],[f7794,f7883])).

fof(f7794,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_85 ),
    inference(resolution,[],[f6656,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f7884,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_46
    | ~ spl2_85 ),
    inference(backward_demodulation,[],[f7805,f7883])).

fof(f7805,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(sK1,sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_85 ),
    inference(resolution,[],[f6656,f472])).

fof(f472,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k3_subset_1(X2,k3_subset_1(X2,X3)) = k7_subset_1(X2,X2,k3_subset_1(X2,X3)) ) ),
    inference(backward_demodulation,[],[f187,f427])).

fof(f187,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X2,k3_subset_1(X2,X3)) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k3_subset_1(X2,X3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f99,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f6670,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f63,f478])).

fof(f478,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f219,f427])).

fof(f219,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f120,f101])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f7652,plain,
    ( spl2_85
    | ~ spl2_46
    | ~ spl2_55 ),
    inference(avatar_split_clause,[],[f4740,f3336,f2750,f6654])).

fof(f4740,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_46
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f4632,f4185])).

fof(f4185,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_46
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f4158,f4178])).

fof(f4178,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_46
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f4164,f2752])).

fof(f4164,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_55 ),
    inference(unit_resulting_resolution,[],[f3338,f463])).

fof(f463,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f186,f427])).

fof(f186,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f99,f87])).

fof(f3338,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f3336])).

fof(f4158,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_55 ),
    inference(unit_resulting_resolution,[],[f3338,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f81,f87])).

fof(f4632,plain,
    ( m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_46 ),
    inference(superposition,[],[f561,f2752])).

fof(f561,plain,(
    ! [X0,X1] : m1_subset_1(k3_subset_1(X0,k7_subset_1(X0,X0,X1)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f460,f79])).

fof(f460,plain,(
    ! [X0,X1] : m1_subset_1(k7_subset_1(X0,X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f132,f427])).

fof(f132,plain,(
    ! [X0,X1] : m1_subset_1(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f96,f87])).

fof(f6657,plain,
    ( spl2_85
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f2999,f2739,f6654])).

fof(f2739,plain,
    ( spl2_44
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f2999,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_44 ),
    inference(superposition,[],[f460,f2741])).

fof(f2741,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f2739])).

fof(f3376,plain,
    ( spl2_56
    | ~ spl2_46 ),
    inference(avatar_split_clause,[],[f3012,f2750,f3373])).

fof(f3012,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_46 ),
    inference(superposition,[],[f452,f2752])).

fof(f452,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f96,f427])).

fof(f3349,plain,
    ( ~ spl2_5
    | ~ spl2_2
    | ~ spl2_3
    | spl2_8 ),
    inference(avatar_split_clause,[],[f3340,f251,f118,f113,f140])).

fof(f140,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f113,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f3340,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_3
    | spl2_8 ),
    inference(subsumption_resolution,[],[f836,f253])).

fof(f253,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f251])).

fof(f836,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f218,f120])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_2 ),
    inference(resolution,[],[f70,f115])).

fof(f115,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f2753,plain,
    ( spl2_46
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f653,f419,f118,f2750])).

fof(f419,plain,
    ( spl2_16
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f653,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(superposition,[],[f421,f478])).

fof(f421,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f419])).

fof(f2742,plain,
    ( spl2_44
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f559,f144,f118,f2739])).

fof(f144,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f559,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f478,f146])).

fof(f146,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f144])).

fof(f2737,plain,
    ( spl2_43
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f282,f257,f118,f113,f2734])).

fof(f257,plain,
    ( spl2_9
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f282,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f273,f248])).

fof(f248,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f115,f120,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f273,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f120,f259,f104])).

fof(f259,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f257])).

fof(f422,plain,
    ( spl2_16
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f246,f118,f113,f419])).

fof(f246,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f115,f120,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f260,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f170,f118,f113,f257])).

fof(f170,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f115,f120,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f217,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f167,f118,f113,f108,f214])).

fof(f108,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f167,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f110,f115,f120,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f110,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f147,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f62,f144,f140])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f121,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f61,f118])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f116,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f60,f113])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f111,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f59,f108])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (27278)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.44  % (27272)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (27269)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (27265)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (27276)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (27270)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (27274)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (27280)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (27279)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (27266)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (27273)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (27277)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (27281)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (27275)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (27268)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (27267)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.51  % (27271)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (27282)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.15/1.03  % (27269)Time limit reached!
% 5.15/1.03  % (27269)------------------------------
% 5.15/1.03  % (27269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.15/1.03  % (27269)Termination reason: Time limit
% 5.15/1.03  
% 5.15/1.03  % (27269)Memory used [KB]: 12281
% 5.15/1.03  % (27269)Time elapsed: 0.612 s
% 5.15/1.03  % (27269)------------------------------
% 5.15/1.03  % (27269)------------------------------
% 5.60/1.16  % (27280)Refutation found. Thanks to Tanya!
% 5.60/1.16  % SZS status Theorem for theBenchmark
% 6.45/1.17  % SZS output start Proof for theBenchmark
% 6.45/1.17  fof(f8111,plain,(
% 6.45/1.17    $false),
% 6.45/1.17    inference(avatar_sat_refutation,[],[f111,f116,f121,f147,f217,f260,f422,f2737,f2742,f2753,f3349,f3376,f6657,f7652,f8006,f8037])).
% 6.45/1.17  fof(f8037,plain,(
% 6.45/1.17    ~spl2_8 | ~spl2_43 | spl2_55),
% 6.45/1.17    inference(avatar_contradiction_clause,[],[f8036])).
% 6.45/1.17  fof(f8036,plain,(
% 6.45/1.17    $false | (~spl2_8 | ~spl2_43 | spl2_55)),
% 6.45/1.17    inference(subsumption_resolution,[],[f3337,f6681])).
% 6.45/1.17  fof(f6681,plain,(
% 6.45/1.17    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_8 | ~spl2_43)),
% 6.45/1.17    inference(backward_demodulation,[],[f2988,f252])).
% 6.45/1.17  fof(f252,plain,(
% 6.45/1.17    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_8),
% 6.45/1.17    inference(avatar_component_clause,[],[f251])).
% 6.45/1.17  fof(f251,plain,(
% 6.45/1.17    spl2_8 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 6.45/1.17  fof(f2988,plain,(
% 6.45/1.17    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_43),
% 6.45/1.17    inference(superposition,[],[f210,f2736])).
% 6.45/1.17  fof(f2736,plain,(
% 6.45/1.17    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_43),
% 6.45/1.17    inference(avatar_component_clause,[],[f2734])).
% 6.45/1.17  fof(f2734,plain,(
% 6.45/1.17    spl2_43 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 6.45/1.17  fof(f210,plain,(
% 6.45/1.17    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 6.45/1.17    inference(forward_demodulation,[],[f204,f98])).
% 6.45/1.17  fof(f98,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 6.45/1.17    inference(definition_unfolding,[],[f78,f75,f93,f75])).
% 6.45/1.17  fof(f93,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 6.45/1.17    inference(definition_unfolding,[],[f77,f74])).
% 6.45/1.17  fof(f74,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f20])).
% 6.45/1.17  fof(f20,axiom,(
% 6.45/1.17    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 6.45/1.17  fof(f77,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f1])).
% 6.45/1.17  fof(f1,axiom,(
% 6.45/1.17    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.45/1.17  fof(f75,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f12])).
% 6.45/1.17  fof(f12,axiom,(
% 6.45/1.17    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 6.45/1.17  fof(f78,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 6.45/1.17    inference(cnf_transformation,[],[f6])).
% 6.45/1.17  fof(f6,axiom,(
% 6.45/1.17    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 6.45/1.17  fof(f204,plain,(
% 6.45/1.17    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f136,f103])).
% 6.45/1.17  fof(f103,plain,(
% 6.45/1.17    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) | r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 6.45/1.17    inference(definition_unfolding,[],[f90,f75,f93])).
% 6.45/1.17  fof(f90,plain,(
% 6.45/1.17    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 6.45/1.17    inference(cnf_transformation,[],[f48])).
% 6.45/1.17  fof(f48,plain,(
% 6.45/1.17    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.45/1.17    inference(ennf_transformation,[],[f9])).
% 6.45/1.17  fof(f9,axiom,(
% 6.45/1.17    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 6.45/1.17  fof(f136,plain,(
% 6.45/1.17    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 6.45/1.17    inference(forward_demodulation,[],[f135,f105])).
% 6.45/1.17  fof(f105,plain,(
% 6.45/1.17    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.45/1.17    inference(forward_demodulation,[],[f95,f94])).
% 6.45/1.17  fof(f94,plain,(
% 6.45/1.17    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 6.45/1.17    inference(definition_unfolding,[],[f65,f74])).
% 6.45/1.17  fof(f65,plain,(
% 6.45/1.17    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 6.45/1.17    inference(cnf_transformation,[],[f3])).
% 6.45/1.17  fof(f3,axiom,(
% 6.45/1.17    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 6.45/1.17  fof(f95,plain,(
% 6.45/1.17    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 6.45/1.17    inference(definition_unfolding,[],[f66,f93])).
% 6.45/1.17  fof(f66,plain,(
% 6.45/1.17    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.45/1.17    inference(cnf_transformation,[],[f7])).
% 6.45/1.17  fof(f7,axiom,(
% 6.45/1.17    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 6.45/1.17  fof(f135,plain,(
% 6.45/1.17    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 6.45/1.17    inference(superposition,[],[f96,f94])).
% 6.45/1.17  fof(f96,plain,(
% 6.45/1.17    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 6.45/1.17    inference(definition_unfolding,[],[f72,f93])).
% 6.45/1.17  fof(f72,plain,(
% 6.45/1.17    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.45/1.17    inference(cnf_transformation,[],[f4])).
% 6.45/1.17  fof(f4,axiom,(
% 6.45/1.17    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.45/1.17  fof(f3337,plain,(
% 6.45/1.17    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_55),
% 6.45/1.17    inference(avatar_component_clause,[],[f3336])).
% 6.45/1.17  fof(f3336,plain,(
% 6.45/1.17    spl2_55 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 6.45/1.17  fof(f8006,plain,(
% 6.45/1.17    ~spl2_3 | ~spl2_7 | ~spl2_43 | ~spl2_46 | ~spl2_56 | ~spl2_85),
% 6.45/1.17    inference(avatar_contradiction_clause,[],[f8005])).
% 6.45/1.17  fof(f8005,plain,(
% 6.45/1.17    $false | (~spl2_3 | ~spl2_7 | ~spl2_43 | ~spl2_46 | ~spl2_56 | ~spl2_85)),
% 6.45/1.17    inference(subsumption_resolution,[],[f8004,f7915])).
% 6.45/1.17  fof(f7915,plain,(
% 6.45/1.17    v4_pre_topc(sK1,sK0) | (~spl2_7 | ~spl2_43 | ~spl2_46 | ~spl2_56 | ~spl2_85)),
% 6.45/1.17    inference(backward_demodulation,[],[f216,f7914])).
% 6.45/1.17  fof(f7914,plain,(
% 6.45/1.17    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_43 | ~spl2_46 | ~spl2_56 | ~spl2_85)),
% 6.45/1.17    inference(forward_demodulation,[],[f3342,f7911])).
% 6.45/1.17  fof(f7911,plain,(
% 6.45/1.17    sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) | (~spl2_46 | ~spl2_56 | ~spl2_85)),
% 6.45/1.17    inference(forward_demodulation,[],[f7772,f7891])).
% 6.45/1.17  fof(f7891,plain,(
% 6.45/1.17    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_46 | ~spl2_85)),
% 6.45/1.17    inference(forward_demodulation,[],[f7797,f7883])).
% 6.45/1.17  fof(f7883,plain,(
% 6.45/1.17    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_46 | ~spl2_85)),
% 6.45/1.17    inference(forward_demodulation,[],[f7803,f2752])).
% 6.45/1.17  fof(f2752,plain,(
% 6.45/1.17    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_46),
% 6.45/1.17    inference(avatar_component_clause,[],[f2750])).
% 6.45/1.17  fof(f2750,plain,(
% 6.45/1.17    spl2_46 <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 6.45/1.17  fof(f7803,plain,(
% 6.45/1.17    k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_85),
% 6.45/1.17    inference(resolution,[],[f6656,f455])).
% 6.45/1.17  fof(f455,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 6.45/1.17    inference(backward_demodulation,[],[f99,f427])).
% 6.45/1.17  fof(f427,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f180,f101])).
% 6.45/1.17  fof(f101,plain,(
% 6.45/1.17    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 6.45/1.17    inference(definition_unfolding,[],[f88,f93])).
% 6.45/1.17  fof(f88,plain,(
% 6.45/1.17    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f46])).
% 6.45/1.17  fof(f46,plain,(
% 6.45/1.17    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.45/1.17    inference(ennf_transformation,[],[f18])).
% 6.45/1.17  fof(f18,axiom,(
% 6.45/1.17    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 6.45/1.17  fof(f180,plain,(
% 6.45/1.17    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f136,f87])).
% 6.45/1.17  fof(f87,plain,(
% 6.45/1.17    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.45/1.17    inference(cnf_transformation,[],[f58])).
% 6.45/1.17  fof(f58,plain,(
% 6.45/1.17    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.45/1.17    inference(nnf_transformation,[],[f21])).
% 6.45/1.17  fof(f21,axiom,(
% 6.45/1.17    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 6.45/1.17  fof(f99,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 6.45/1.17    inference(definition_unfolding,[],[f80,f93])).
% 6.45/1.17  fof(f80,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f38])).
% 6.45/1.17  fof(f38,plain,(
% 6.45/1.17    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.45/1.17    inference(ennf_transformation,[],[f14])).
% 6.45/1.17  fof(f14,axiom,(
% 6.45/1.17    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 6.45/1.17  fof(f6656,plain,(
% 6.45/1.17    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_85),
% 6.45/1.17    inference(avatar_component_clause,[],[f6654])).
% 6.45/1.17  fof(f6654,plain,(
% 6.45/1.17    spl2_85 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).
% 6.45/1.17  fof(f7797,plain,(
% 6.45/1.17    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_85),
% 6.45/1.17    inference(resolution,[],[f6656,f106])).
% 6.45/1.17  fof(f106,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 6.45/1.17    inference(forward_demodulation,[],[f82,f64])).
% 6.45/1.17  fof(f64,plain,(
% 6.45/1.17    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 6.45/1.17    inference(cnf_transformation,[],[f13])).
% 6.45/1.17  fof(f13,axiom,(
% 6.45/1.17    ! [X0] : k2_subset_1(X0) = X0),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 6.45/1.17  fof(f82,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f40])).
% 6.45/1.17  fof(f40,plain,(
% 6.45/1.17    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.45/1.17    inference(ennf_transformation,[],[f19])).
% 6.45/1.17  fof(f19,axiom,(
% 6.45/1.17    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 6.45/1.17  fof(f7772,plain,(
% 6.45/1.17    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_56 | ~spl2_85)),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f3375,f6656,f242])).
% 6.45/1.17  fof(f242,plain,(
% 6.45/1.17    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~r1_tarski(X2,X0)) )),
% 6.45/1.17    inference(resolution,[],[f104,f87])).
% 6.45/1.17  fof(f104,plain,(
% 6.45/1.17    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(definition_unfolding,[],[f92,f75])).
% 6.45/1.17  fof(f92,plain,(
% 6.45/1.17    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f52])).
% 6.45/1.17  fof(f52,plain,(
% 6.45/1.17    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.45/1.17    inference(flattening,[],[f51])).
% 6.45/1.17  fof(f51,plain,(
% 6.45/1.17    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.45/1.17    inference(ennf_transformation,[],[f17])).
% 6.45/1.17  fof(f17,axiom,(
% 6.45/1.17    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 6.45/1.17  fof(f3375,plain,(
% 6.45/1.17    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_56),
% 6.45/1.17    inference(avatar_component_clause,[],[f3373])).
% 6.45/1.17  fof(f3373,plain,(
% 6.45/1.17    spl2_56 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 6.45/1.17  fof(f3342,plain,(
% 6.45/1.17    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) | (~spl2_43 | ~spl2_46)),
% 6.45/1.17    inference(forward_demodulation,[],[f3341,f2736])).
% 6.45/1.17  fof(f3341,plain,(
% 6.45/1.17    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_46),
% 6.45/1.17    inference(forward_demodulation,[],[f3014,f73])).
% 6.45/1.17  fof(f73,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.45/1.17    inference(cnf_transformation,[],[f11])).
% 6.45/1.17  fof(f11,axiom,(
% 6.45/1.17    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 6.45/1.17  fof(f3014,plain,(
% 6.45/1.17    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_46),
% 6.45/1.17    inference(superposition,[],[f454,f2752])).
% 6.45/1.17  fof(f454,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k7_subset_1(X1,X1,X0)))) )),
% 6.45/1.17    inference(backward_demodulation,[],[f98,f427])).
% 6.45/1.17  fof(f216,plain,(
% 6.45/1.17    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_7),
% 6.45/1.17    inference(avatar_component_clause,[],[f214])).
% 6.45/1.17  fof(f214,plain,(
% 6.45/1.17    spl2_7 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 6.45/1.17  fof(f8004,plain,(
% 6.45/1.17    ~v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_46 | ~spl2_85)),
% 6.45/1.17    inference(subsumption_resolution,[],[f6670,f7896])).
% 6.45/1.17  fof(f7896,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_46 | ~spl2_85)),
% 6.45/1.17    inference(backward_demodulation,[],[f7884,f7892])).
% 6.45/1.17  fof(f7892,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_46 | ~spl2_85)),
% 6.45/1.17    inference(forward_demodulation,[],[f7794,f7883])).
% 6.45/1.17  fof(f7794,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_85),
% 6.45/1.17    inference(resolution,[],[f6656,f81])).
% 6.45/1.17  fof(f81,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 6.45/1.17    inference(cnf_transformation,[],[f39])).
% 6.45/1.17  fof(f39,plain,(
% 6.45/1.17    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.45/1.17    inference(ennf_transformation,[],[f16])).
% 6.45/1.17  fof(f16,axiom,(
% 6.45/1.17    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 6.45/1.17  fof(f7884,plain,(
% 6.45/1.17    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_46 | ~spl2_85)),
% 6.45/1.17    inference(backward_demodulation,[],[f7805,f7883])).
% 6.45/1.17  fof(f7805,plain,(
% 6.45/1.17    k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(sK1,sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_85),
% 6.45/1.17    inference(resolution,[],[f6656,f472])).
% 6.45/1.17  fof(f472,plain,(
% 6.45/1.17    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k3_subset_1(X2,k3_subset_1(X2,X3)) = k7_subset_1(X2,X2,k3_subset_1(X2,X3))) )),
% 6.45/1.17    inference(backward_demodulation,[],[f187,f427])).
% 6.45/1.17  fof(f187,plain,(
% 6.45/1.17    ( ! [X2,X3] : (k3_subset_1(X2,k3_subset_1(X2,X3)) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k3_subset_1(X2,X3)))) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 6.45/1.17    inference(resolution,[],[f99,f79])).
% 6.45/1.17  fof(f79,plain,(
% 6.45/1.17    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f37])).
% 6.45/1.17  fof(f37,plain,(
% 6.45/1.17    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.45/1.17    inference(ennf_transformation,[],[f15])).
% 6.45/1.17  fof(f15,axiom,(
% 6.45/1.17    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 6.45/1.17  fof(f6670,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_3),
% 6.45/1.17    inference(forward_demodulation,[],[f63,f478])).
% 6.45/1.17  fof(f478,plain,(
% 6.45/1.17    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) ) | ~spl2_3),
% 6.45/1.17    inference(backward_demodulation,[],[f219,f427])).
% 6.45/1.17  fof(f219,plain,(
% 6.45/1.17    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f120,f101])).
% 6.45/1.17  fof(f120,plain,(
% 6.45/1.17    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 6.45/1.17    inference(avatar_component_clause,[],[f118])).
% 6.45/1.17  fof(f118,plain,(
% 6.45/1.17    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 6.45/1.17  fof(f63,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 6.45/1.17    inference(cnf_transformation,[],[f57])).
% 6.45/1.17  fof(f57,plain,(
% 6.45/1.17    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 6.45/1.17    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).
% 6.45/1.17  fof(f55,plain,(
% 6.45/1.17    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 6.45/1.17    introduced(choice_axiom,[])).
% 6.45/1.17  fof(f56,plain,(
% 6.45/1.17    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.45/1.17    introduced(choice_axiom,[])).
% 6.45/1.17  fof(f54,plain,(
% 6.45/1.17    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.45/1.17    inference(flattening,[],[f53])).
% 6.45/1.17  fof(f53,plain,(
% 6.45/1.17    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.45/1.17    inference(nnf_transformation,[],[f31])).
% 6.45/1.17  fof(f31,plain,(
% 6.45/1.17    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.45/1.17    inference(flattening,[],[f30])).
% 6.45/1.17  fof(f30,plain,(
% 6.45/1.17    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.45/1.17    inference(ennf_transformation,[],[f29])).
% 6.45/1.17  fof(f29,negated_conjecture,(
% 6.45/1.17    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 6.45/1.17    inference(negated_conjecture,[],[f28])).
% 6.45/1.17  fof(f28,conjecture,(
% 6.45/1.17    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 6.45/1.17  fof(f7652,plain,(
% 6.45/1.17    spl2_85 | ~spl2_46 | ~spl2_55),
% 6.45/1.17    inference(avatar_split_clause,[],[f4740,f3336,f2750,f6654])).
% 6.45/1.17  fof(f4740,plain,(
% 6.45/1.17    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl2_46 | ~spl2_55)),
% 6.45/1.17    inference(forward_demodulation,[],[f4632,f4185])).
% 6.45/1.17  fof(f4185,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_46 | ~spl2_55)),
% 6.45/1.17    inference(forward_demodulation,[],[f4158,f4178])).
% 6.45/1.17  fof(f4178,plain,(
% 6.45/1.17    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_46 | ~spl2_55)),
% 6.45/1.17    inference(forward_demodulation,[],[f4164,f2752])).
% 6.45/1.17  fof(f4164,plain,(
% 6.45/1.17    k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_55),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f3338,f463])).
% 6.45/1.17  fof(f463,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 6.45/1.17    inference(backward_demodulation,[],[f186,f427])).
% 6.45/1.17  fof(f186,plain,(
% 6.45/1.17    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X1,X0)) )),
% 6.45/1.17    inference(resolution,[],[f99,f87])).
% 6.45/1.17  fof(f3338,plain,(
% 6.45/1.17    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_55),
% 6.45/1.17    inference(avatar_component_clause,[],[f3336])).
% 6.45/1.17  fof(f4158,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_55),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f3338,f155])).
% 6.45/1.17  fof(f155,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 6.45/1.17    inference(resolution,[],[f81,f87])).
% 6.45/1.17  fof(f4632,plain,(
% 6.45/1.17    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl2_46),
% 6.45/1.17    inference(superposition,[],[f561,f2752])).
% 6.45/1.17  fof(f561,plain,(
% 6.45/1.17    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,k7_subset_1(X0,X0,X1)),k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f460,f79])).
% 6.45/1.17  fof(f460,plain,(
% 6.45/1.17    ( ! [X0,X1] : (m1_subset_1(k7_subset_1(X0,X0,X1),k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(backward_demodulation,[],[f132,f427])).
% 6.45/1.17  fof(f132,plain,(
% 6.45/1.17    ( ! [X0,X1] : (m1_subset_1(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_zfmisc_1(X0))) )),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f96,f87])).
% 6.45/1.17  fof(f6657,plain,(
% 6.45/1.17    spl2_85 | ~spl2_44),
% 6.45/1.17    inference(avatar_split_clause,[],[f2999,f2739,f6654])).
% 6.45/1.17  fof(f2739,plain,(
% 6.45/1.17    spl2_44 <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 6.45/1.17  fof(f2999,plain,(
% 6.45/1.17    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_44),
% 6.45/1.17    inference(superposition,[],[f460,f2741])).
% 6.45/1.17  fof(f2741,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~spl2_44),
% 6.45/1.17    inference(avatar_component_clause,[],[f2739])).
% 6.45/1.17  fof(f3376,plain,(
% 6.45/1.17    spl2_56 | ~spl2_46),
% 6.45/1.17    inference(avatar_split_clause,[],[f3012,f2750,f3373])).
% 6.45/1.17  fof(f3012,plain,(
% 6.45/1.17    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_46),
% 6.45/1.17    inference(superposition,[],[f452,f2752])).
% 6.45/1.17  fof(f452,plain,(
% 6.45/1.17    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) )),
% 6.45/1.17    inference(backward_demodulation,[],[f96,f427])).
% 6.45/1.17  fof(f3349,plain,(
% 6.45/1.17    ~spl2_5 | ~spl2_2 | ~spl2_3 | spl2_8),
% 6.45/1.17    inference(avatar_split_clause,[],[f3340,f251,f118,f113,f140])).
% 6.45/1.17  fof(f140,plain,(
% 6.45/1.17    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 6.45/1.17  fof(f113,plain,(
% 6.45/1.17    spl2_2 <=> l1_pre_topc(sK0)),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 6.45/1.17  fof(f3340,plain,(
% 6.45/1.17    ~v4_pre_topc(sK1,sK0) | (~spl2_2 | ~spl2_3 | spl2_8)),
% 6.45/1.17    inference(subsumption_resolution,[],[f836,f253])).
% 6.45/1.17  fof(f253,plain,(
% 6.45/1.17    sK1 != k2_pre_topc(sK0,sK1) | spl2_8),
% 6.45/1.17    inference(avatar_component_clause,[],[f251])).
% 6.45/1.17  fof(f836,plain,(
% 6.45/1.17    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3)),
% 6.45/1.17    inference(resolution,[],[f218,f120])).
% 6.45/1.17  fof(f218,plain,(
% 6.45/1.17    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_2),
% 6.45/1.17    inference(resolution,[],[f70,f115])).
% 6.45/1.17  fof(f115,plain,(
% 6.45/1.17    l1_pre_topc(sK0) | ~spl2_2),
% 6.45/1.17    inference(avatar_component_clause,[],[f113])).
% 6.45/1.17  fof(f70,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 6.45/1.17    inference(cnf_transformation,[],[f36])).
% 6.45/1.17  fof(f36,plain,(
% 6.45/1.17    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.45/1.17    inference(flattening,[],[f35])).
% 6.45/1.17  fof(f35,plain,(
% 6.45/1.17    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.45/1.17    inference(ennf_transformation,[],[f22])).
% 6.45/1.17  fof(f22,axiom,(
% 6.45/1.17    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 6.45/1.17  fof(f2753,plain,(
% 6.45/1.17    spl2_46 | ~spl2_3 | ~spl2_16),
% 6.45/1.17    inference(avatar_split_clause,[],[f653,f419,f118,f2750])).
% 6.45/1.17  fof(f419,plain,(
% 6.45/1.17    spl2_16 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 6.45/1.17  fof(f653,plain,(
% 6.45/1.17    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_16)),
% 6.45/1.17    inference(superposition,[],[f421,f478])).
% 6.45/1.17  fof(f421,plain,(
% 6.45/1.17    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_16),
% 6.45/1.17    inference(avatar_component_clause,[],[f419])).
% 6.45/1.17  fof(f2742,plain,(
% 6.45/1.17    spl2_44 | ~spl2_3 | ~spl2_6),
% 6.45/1.17    inference(avatar_split_clause,[],[f559,f144,f118,f2739])).
% 6.45/1.17  fof(f144,plain,(
% 6.45/1.17    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 6.45/1.17  fof(f559,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 6.45/1.17    inference(superposition,[],[f478,f146])).
% 6.45/1.17  fof(f146,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 6.45/1.17    inference(avatar_component_clause,[],[f144])).
% 6.45/1.17  fof(f2737,plain,(
% 6.45/1.17    spl2_43 | ~spl2_2 | ~spl2_3 | ~spl2_9),
% 6.45/1.17    inference(avatar_split_clause,[],[f282,f257,f118,f113,f2734])).
% 6.45/1.17  fof(f257,plain,(
% 6.45/1.17    spl2_9 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 6.45/1.17  fof(f282,plain,(
% 6.45/1.17    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3 | ~spl2_9)),
% 6.45/1.17    inference(forward_demodulation,[],[f273,f248])).
% 6.45/1.17  fof(f248,plain,(
% 6.45/1.17    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f115,f120,f69])).
% 6.45/1.17  fof(f69,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f34])).
% 6.45/1.17  fof(f34,plain,(
% 6.45/1.17    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.45/1.17    inference(ennf_transformation,[],[f26])).
% 6.45/1.17  fof(f26,axiom,(
% 6.45/1.17    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 6.45/1.17  fof(f273,plain,(
% 6.45/1.17    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_9)),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f120,f259,f104])).
% 6.45/1.17  fof(f259,plain,(
% 6.45/1.17    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 6.45/1.17    inference(avatar_component_clause,[],[f257])).
% 6.45/1.17  fof(f422,plain,(
% 6.45/1.17    spl2_16 | ~spl2_2 | ~spl2_3),
% 6.45/1.17    inference(avatar_split_clause,[],[f246,f118,f113,f419])).
% 6.45/1.17  fof(f246,plain,(
% 6.45/1.17    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f115,f120,f68])).
% 6.45/1.17  fof(f68,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 6.45/1.17    inference(cnf_transformation,[],[f33])).
% 6.45/1.17  fof(f33,plain,(
% 6.45/1.17    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.45/1.17    inference(ennf_transformation,[],[f27])).
% 6.45/1.17  fof(f27,axiom,(
% 6.45/1.17    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 6.45/1.17  fof(f260,plain,(
% 6.45/1.17    spl2_9 | ~spl2_2 | ~spl2_3),
% 6.45/1.17    inference(avatar_split_clause,[],[f170,f118,f113,f257])).
% 6.45/1.17  fof(f170,plain,(
% 6.45/1.17    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f115,f120,f85])).
% 6.45/1.17  fof(f85,plain,(
% 6.45/1.17    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.45/1.17    inference(cnf_transformation,[],[f45])).
% 6.45/1.17  fof(f45,plain,(
% 6.45/1.17    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 6.45/1.17    inference(flattening,[],[f44])).
% 6.45/1.17  fof(f44,plain,(
% 6.45/1.17    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 6.45/1.17    inference(ennf_transformation,[],[f23])).
% 6.45/1.17  fof(f23,axiom,(
% 6.45/1.17    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 6.45/1.17  fof(f217,plain,(
% 6.45/1.17    spl2_7 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 6.45/1.17    inference(avatar_split_clause,[],[f167,f118,f113,f108,f214])).
% 6.45/1.17  fof(f108,plain,(
% 6.45/1.17    spl2_1 <=> v2_pre_topc(sK0)),
% 6.45/1.17    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 6.45/1.17  fof(f167,plain,(
% 6.45/1.17    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 6.45/1.17    inference(unit_resulting_resolution,[],[f110,f115,f120,f84])).
% 6.45/1.17  fof(f84,plain,(
% 6.45/1.17    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 6.45/1.17    inference(cnf_transformation,[],[f43])).
% 6.45/1.17  fof(f43,plain,(
% 6.45/1.17    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.45/1.17    inference(flattening,[],[f42])).
% 6.45/1.17  fof(f42,plain,(
% 6.45/1.17    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.45/1.17    inference(ennf_transformation,[],[f24])).
% 6.45/1.17  fof(f24,axiom,(
% 6.45/1.17    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 6.45/1.17    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 6.45/1.17  fof(f110,plain,(
% 6.45/1.17    v2_pre_topc(sK0) | ~spl2_1),
% 6.45/1.17    inference(avatar_component_clause,[],[f108])).
% 6.45/1.17  fof(f147,plain,(
% 6.45/1.17    spl2_5 | spl2_6),
% 6.45/1.17    inference(avatar_split_clause,[],[f62,f144,f140])).
% 6.45/1.17  fof(f62,plain,(
% 6.45/1.17    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 6.45/1.17    inference(cnf_transformation,[],[f57])).
% 6.45/1.17  fof(f121,plain,(
% 6.45/1.17    spl2_3),
% 6.45/1.17    inference(avatar_split_clause,[],[f61,f118])).
% 6.45/1.17  fof(f61,plain,(
% 6.45/1.17    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.45/1.17    inference(cnf_transformation,[],[f57])).
% 6.45/1.17  fof(f116,plain,(
% 6.45/1.17    spl2_2),
% 6.45/1.17    inference(avatar_split_clause,[],[f60,f113])).
% 6.45/1.17  fof(f60,plain,(
% 6.45/1.17    l1_pre_topc(sK0)),
% 6.45/1.17    inference(cnf_transformation,[],[f57])).
% 6.45/1.17  fof(f111,plain,(
% 6.45/1.17    spl2_1),
% 6.45/1.17    inference(avatar_split_clause,[],[f59,f108])).
% 6.45/1.17  fof(f59,plain,(
% 6.45/1.17    v2_pre_topc(sK0)),
% 6.45/1.17    inference(cnf_transformation,[],[f57])).
% 6.45/1.17  % SZS output end Proof for theBenchmark
% 6.45/1.17  % (27280)------------------------------
% 6.45/1.17  % (27280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.45/1.17  % (27280)Termination reason: Refutation
% 6.45/1.17  
% 6.45/1.17  % (27280)Memory used [KB]: 18293
% 6.45/1.17  % (27280)Time elapsed: 0.725 s
% 6.45/1.17  % (27280)------------------------------
% 6.45/1.17  % (27280)------------------------------
% 6.45/1.17  % (27264)Success in time 0.818 s
%------------------------------------------------------------------------------
