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
% DateTime   : Thu Dec  3 13:11:53 EST 2020

% Result     : Theorem 5.22s
% Output     : Refutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :  185 (1100 expanded)
%              Number of leaves         :   41 ( 377 expanded)
%              Depth                    :   16
%              Number of atoms          :  495 (1989 expanded)
%              Number of equality atoms :  120 ( 836 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f118,f123,f159,f215,f301,f723,f3027,f3032,f3046,f3098,f3282,f3585,f3590,f3600,f3976,f4130,f8309])).

fof(f8309,plain,
    ( ~ spl2_3
    | ~ spl2_7
    | ~ spl2_44
    | ~ spl2_47
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_55
    | ~ spl2_56
    | ~ spl2_63 ),
    inference(avatar_contradiction_clause,[],[f8308])).

fof(f8308,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_7
    | ~ spl2_44
    | ~ spl2_47
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_54
    | ~ spl2_55
    | ~ spl2_56
    | ~ spl2_63 ),
    inference(subsumption_resolution,[],[f8307,f8228])).

fof(f8228,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_7
    | ~ spl2_44
    | ~ spl2_47
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_56
    | ~ spl2_63 ),
    inference(backward_demodulation,[],[f214,f8227])).

fof(f8227,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_44
    | ~ spl2_47
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_56
    | ~ spl2_63 ),
    inference(backward_demodulation,[],[f8222,f8226])).

fof(f8226,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_56
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f8225,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f8225,plain,
    ( sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_48
    | ~ spl2_51
    | ~ spl2_56
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f3604,f8220])).

fof(f8220,plain,
    ( sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_48
    | ~ spl2_56
    | ~ spl2_63 ),
    inference(forward_demodulation,[],[f8035,f3599])).

fof(f3599,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f3597])).

fof(f3597,plain,
    ( spl2_56
  <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f8035,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_48
    | ~ spl2_63 ),
    inference(unit_resulting_resolution,[],[f4129,f3097,f269])).

fof(f269,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f106,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f93,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f3097,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f3095])).

fof(f3095,plain,
    ( spl2_48
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f4129,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f4127])).

fof(f4127,plain,
    ( spl2_63
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f3604,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl2_51 ),
    inference(superposition,[],[f474,f3281])).

fof(f3281,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f3279])).

fof(f3279,plain,
    ( spl2_51
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f474,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k7_subset_1(X1,X1,X0))) ),
    inference(backward_demodulation,[],[f100,f447])).

fof(f447,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f190,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f89,f94])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f78,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f190,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f139,f88])).

fof(f139,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f137,f107])).

fof(f107,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f96,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f96,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f67,f94])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f137,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f98,f95])).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f73,f94])).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f100,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(definition_unfolding,[],[f79,f76,f94,f76])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f8222,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_44
    | ~ spl2_47
    | ~ spl2_48 ),
    inference(backward_demodulation,[],[f8006,f3086])).

fof(f3086,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_44
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f3069,f3026])).

fof(f3026,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f3024])).

fof(f3024,plain,
    ( spl2_44
  <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f3069,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f190,f3045,f269])).

fof(f3045,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f3043])).

fof(f3043,plain,
    ( spl2_47
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f8006,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_48 ),
    inference(unit_resulting_resolution,[],[f190,f3097,f106])).

fof(f214,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl2_7
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f8307,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_48
    | ~ spl2_54
    | ~ spl2_55 ),
    inference(subsumption_resolution,[],[f3033,f8216])).

fof(f8216,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_54
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f8215,f3589])).

fof(f3589,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f3587])).

fof(f3587,plain,
    ( spl2_55
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f8215,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_48
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f8065,f3584])).

fof(f3584,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f3582])).

fof(f3582,plain,
    ( spl2_54
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f8065,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(sK1,sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_48 ),
    inference(resolution,[],[f3097,f496])).

fof(f496,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k3_subset_1(X2,k3_subset_1(X2,X3)) = k7_subset_1(X2,X2,k3_subset_1(X2,X3)) ) ),
    inference(backward_demodulation,[],[f206,f447])).

fof(f206,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X2,k3_subset_1(X2,X3)) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k3_subset_1(X2,X3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f101,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f81,f94])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3033,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f64,f502])).

fof(f502,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f244,f447])).

fof(f244,plain,
    ( ! [X0] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f122,f103])).

fof(f122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).

fof(f56,plain,
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

fof(f57,plain,
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

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f4130,plain,
    ( spl2_63
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f3602,f3279,f4127])).

fof(f3602,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_51 ),
    inference(superposition,[],[f472,f3281])).

fof(f472,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f98,f447])).

fof(f3976,plain,
    ( spl2_47
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f3527,f3029,f3043])).

fof(f3029,plain,
    ( spl2_45
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f3527,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_45 ),
    inference(superposition,[],[f472,f3031])).

fof(f3031,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f3029])).

fof(f3600,plain,
    ( spl2_56
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f3087,f3043,f720,f120,f3597])).

fof(f720,plain,
    ( spl2_16
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f3087,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f3068,f3083])).

fof(f3083,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f3072,f739])).

fof(f739,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(superposition,[],[f722,f502])).

fof(f722,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f720])).

fof(f3072,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f3045,f484])).

fof(f484,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f205,f447])).

fof(f205,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f101,f88])).

fof(f3068,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f3045,f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(resolution,[],[f108,f88])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f83,f65])).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f3590,plain,
    ( spl2_55
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f3088,f3043,f720,f120,f3587])).

fof(f3088,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_47 ),
    inference(forward_demodulation,[],[f3067,f3083])).

fof(f3067,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f3045,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f82,f88])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f3585,plain,
    ( spl2_54
    | ~ spl2_3
    | ~ spl2_16
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f3083,f3043,f720,f120,f3582])).

fof(f3282,plain,
    ( spl2_51
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f739,f720,f120,f3279])).

fof(f3098,plain,
    ( spl2_48
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f3048,f3043,f3095])).

fof(f3048,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_47 ),
    inference(unit_resulting_resolution,[],[f3045,f88])).

fof(f3046,plain,
    ( spl2_47
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f3035,f152,f120,f115,f3043])).

fof(f115,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f152,plain,
    ( spl2_5
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f3035,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f117,f122,f154,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f154,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f117,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f3032,plain,
    ( spl2_45
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f646,f156,f120,f3029])).

fof(f156,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f646,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f502,f158])).

fof(f158,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f3027,plain,
    ( spl2_44
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f323,f298,f120,f115,f3024])).

fof(f298,plain,
    ( spl2_8
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f323,plain,
    ( k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f314,f295])).

fof(f295,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f117,f122,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f314,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f122,f300,f106])).

fof(f300,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f298])).

fof(f723,plain,
    ( spl2_16
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f273,f120,f115,f720])).

fof(f273,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f117,f122,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f301,plain,
    ( spl2_8
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f195,f120,f115,f298])).

fof(f195,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f117,f122,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f215,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f192,f120,f115,f110,f212])).

fof(f110,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f192,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f112,f117,f122,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f112,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f159,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f63,f156,f152])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f123,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f62,f120])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f118,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f61,f115])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f113,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f60,f110])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:56:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (7219)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (7221)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (7218)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (7229)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (7224)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (7216)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (7222)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (7220)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (7231)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (7230)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (7228)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (7217)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (7225)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (7226)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (7227)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (7223)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (7232)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (7233)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.22/1.03  % (7231)Refutation found. Thanks to Tanya!
% 5.22/1.03  % SZS status Theorem for theBenchmark
% 5.22/1.03  % SZS output start Proof for theBenchmark
% 5.22/1.03  fof(f8314,plain,(
% 5.22/1.03    $false),
% 5.22/1.03    inference(avatar_sat_refutation,[],[f113,f118,f123,f159,f215,f301,f723,f3027,f3032,f3046,f3098,f3282,f3585,f3590,f3600,f3976,f4130,f8309])).
% 5.22/1.03  fof(f8309,plain,(
% 5.22/1.03    ~spl2_3 | ~spl2_7 | ~spl2_44 | ~spl2_47 | ~spl2_48 | ~spl2_51 | ~spl2_54 | ~spl2_55 | ~spl2_56 | ~spl2_63),
% 5.22/1.03    inference(avatar_contradiction_clause,[],[f8308])).
% 5.22/1.03  fof(f8308,plain,(
% 5.22/1.03    $false | (~spl2_3 | ~spl2_7 | ~spl2_44 | ~spl2_47 | ~spl2_48 | ~spl2_51 | ~spl2_54 | ~spl2_55 | ~spl2_56 | ~spl2_63)),
% 5.22/1.03    inference(subsumption_resolution,[],[f8307,f8228])).
% 5.22/1.03  fof(f8228,plain,(
% 5.22/1.03    v4_pre_topc(sK1,sK0) | (~spl2_7 | ~spl2_44 | ~spl2_47 | ~spl2_48 | ~spl2_51 | ~spl2_56 | ~spl2_63)),
% 5.22/1.03    inference(backward_demodulation,[],[f214,f8227])).
% 5.22/1.03  fof(f8227,plain,(
% 5.22/1.03    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_44 | ~spl2_47 | ~spl2_48 | ~spl2_51 | ~spl2_56 | ~spl2_63)),
% 5.22/1.03    inference(backward_demodulation,[],[f8222,f8226])).
% 5.22/1.03  fof(f8226,plain,(
% 5.22/1.03    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_48 | ~spl2_51 | ~spl2_56 | ~spl2_63)),
% 5.22/1.03    inference(forward_demodulation,[],[f8225,f74])).
% 5.22/1.03  fof(f74,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 5.22/1.03    inference(cnf_transformation,[],[f12])).
% 5.22/1.03  fof(f12,axiom,(
% 5.22/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 5.22/1.03  fof(f8225,plain,(
% 5.22/1.03    sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | (~spl2_48 | ~spl2_51 | ~spl2_56 | ~spl2_63)),
% 5.22/1.03    inference(forward_demodulation,[],[f3604,f8220])).
% 5.22/1.03  fof(f8220,plain,(
% 5.22/1.03    sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) | (~spl2_48 | ~spl2_56 | ~spl2_63)),
% 5.22/1.03    inference(forward_demodulation,[],[f8035,f3599])).
% 5.22/1.03  fof(f3599,plain,(
% 5.22/1.03    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_56),
% 5.22/1.03    inference(avatar_component_clause,[],[f3597])).
% 5.22/1.03  fof(f3597,plain,(
% 5.22/1.03    spl2_56 <=> sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 5.22/1.03  fof(f8035,plain,(
% 5.22/1.03    k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) | (~spl2_48 | ~spl2_63)),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f4129,f3097,f269])).
% 5.22/1.03  fof(f269,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~r1_tarski(X2,X0)) )),
% 5.22/1.03    inference(resolution,[],[f106,f88])).
% 5.22/1.03  fof(f88,plain,(
% 5.22/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 5.22/1.03    inference(cnf_transformation,[],[f59])).
% 5.22/1.03  fof(f59,plain,(
% 5.22/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 5.22/1.03    inference(nnf_transformation,[],[f22])).
% 5.22/1.03  fof(f22,axiom,(
% 5.22/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 5.22/1.03  fof(f106,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.22/1.03    inference(definition_unfolding,[],[f93,f76])).
% 5.22/1.03  fof(f76,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f13])).
% 5.22/1.03  fof(f13,axiom,(
% 5.22/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 5.22/1.03  fof(f93,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f53])).
% 5.22/1.03  fof(f53,plain,(
% 5.22/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.22/1.03    inference(flattening,[],[f52])).
% 5.22/1.03  fof(f52,plain,(
% 5.22/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.22/1.03    inference(ennf_transformation,[],[f18])).
% 5.22/1.03  fof(f18,axiom,(
% 5.22/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.22/1.03  fof(f3097,plain,(
% 5.22/1.03    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_48),
% 5.22/1.03    inference(avatar_component_clause,[],[f3095])).
% 5.22/1.03  fof(f3095,plain,(
% 5.22/1.03    spl2_48 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 5.22/1.03  fof(f4129,plain,(
% 5.22/1.03    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_63),
% 5.22/1.03    inference(avatar_component_clause,[],[f4127])).
% 5.22/1.03  fof(f4127,plain,(
% 5.22/1.03    spl2_63 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 5.22/1.03  fof(f3604,plain,(
% 5.22/1.03    k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl2_51),
% 5.22/1.03    inference(superposition,[],[f474,f3281])).
% 5.22/1.03  fof(f3281,plain,(
% 5.22/1.03    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_51),
% 5.22/1.03    inference(avatar_component_clause,[],[f3279])).
% 5.22/1.03  fof(f3279,plain,(
% 5.22/1.03    spl2_51 <=> k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 5.22/1.03  fof(f474,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k7_subset_1(X1,X1,X0)))) )),
% 5.22/1.03    inference(backward_demodulation,[],[f100,f447])).
% 5.22/1.03  fof(f447,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f190,f103])).
% 5.22/1.03  fof(f103,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 5.22/1.03    inference(definition_unfolding,[],[f89,f94])).
% 5.22/1.03  fof(f94,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 5.22/1.03    inference(definition_unfolding,[],[f78,f75])).
% 5.22/1.03  fof(f75,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f21])).
% 5.22/1.03  fof(f21,axiom,(
% 5.22/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 5.22/1.03  fof(f78,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f1])).
% 5.22/1.03  fof(f1,axiom,(
% 5.22/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.22/1.03  fof(f89,plain,(
% 5.22/1.03    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f47])).
% 5.22/1.03  fof(f47,plain,(
% 5.22/1.03    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.22/1.03    inference(ennf_transformation,[],[f19])).
% 5.22/1.03  fof(f19,axiom,(
% 5.22/1.03    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 5.22/1.03  fof(f190,plain,(
% 5.22/1.03    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f139,f88])).
% 5.22/1.03  fof(f139,plain,(
% 5.22/1.03    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 5.22/1.03    inference(forward_demodulation,[],[f137,f107])).
% 5.22/1.03  fof(f107,plain,(
% 5.22/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.22/1.03    inference(forward_demodulation,[],[f96,f95])).
% 5.22/1.03  fof(f95,plain,(
% 5.22/1.03    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 5.22/1.03    inference(definition_unfolding,[],[f66,f75])).
% 5.22/1.03  fof(f66,plain,(
% 5.22/1.03    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 5.22/1.03    inference(cnf_transformation,[],[f3])).
% 5.22/1.03  fof(f3,axiom,(
% 5.22/1.03    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 5.22/1.03  fof(f96,plain,(
% 5.22/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 5.22/1.03    inference(definition_unfolding,[],[f67,f94])).
% 5.22/1.03  fof(f67,plain,(
% 5.22/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.22/1.03    inference(cnf_transformation,[],[f7])).
% 5.22/1.03  fof(f7,axiom,(
% 5.22/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 5.22/1.03  fof(f137,plain,(
% 5.22/1.03    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 5.22/1.03    inference(superposition,[],[f98,f95])).
% 5.22/1.03  fof(f98,plain,(
% 5.22/1.03    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 5.22/1.03    inference(definition_unfolding,[],[f73,f94])).
% 5.22/1.03  fof(f73,plain,(
% 5.22/1.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.22/1.03    inference(cnf_transformation,[],[f4])).
% 5.22/1.03  fof(f4,axiom,(
% 5.22/1.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.22/1.03  fof(f100,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 5.22/1.03    inference(definition_unfolding,[],[f79,f76,f94,f76])).
% 5.22/1.03  fof(f79,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 5.22/1.03    inference(cnf_transformation,[],[f6])).
% 5.22/1.03  fof(f6,axiom,(
% 5.22/1.03    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 5.22/1.03  fof(f8222,plain,(
% 5.22/1.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_44 | ~spl2_47 | ~spl2_48)),
% 5.22/1.03    inference(backward_demodulation,[],[f8006,f3086])).
% 5.22/1.03  fof(f3086,plain,(
% 5.22/1.03    k2_pre_topc(sK0,sK1) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_44 | ~spl2_47)),
% 5.22/1.03    inference(forward_demodulation,[],[f3069,f3026])).
% 5.22/1.03  fof(f3026,plain,(
% 5.22/1.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_44),
% 5.22/1.03    inference(avatar_component_clause,[],[f3024])).
% 5.22/1.03  fof(f3024,plain,(
% 5.22/1.03    spl2_44 <=> k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 5.22/1.03  fof(f3069,plain,(
% 5.22/1.03    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_47),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f190,f3045,f269])).
% 5.22/1.03  fof(f3045,plain,(
% 5.22/1.03    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_47),
% 5.22/1.03    inference(avatar_component_clause,[],[f3043])).
% 5.22/1.03  fof(f3043,plain,(
% 5.22/1.03    spl2_47 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 5.22/1.03  fof(f8006,plain,(
% 5.22/1.03    k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_48),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f190,f3097,f106])).
% 5.22/1.03  fof(f214,plain,(
% 5.22/1.03    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~spl2_7),
% 5.22/1.03    inference(avatar_component_clause,[],[f212])).
% 5.22/1.03  fof(f212,plain,(
% 5.22/1.03    spl2_7 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 5.22/1.03  fof(f8307,plain,(
% 5.22/1.03    ~v4_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_48 | ~spl2_54 | ~spl2_55)),
% 5.22/1.03    inference(subsumption_resolution,[],[f3033,f8216])).
% 5.22/1.03  fof(f8216,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_48 | ~spl2_54 | ~spl2_55)),
% 5.22/1.03    inference(forward_demodulation,[],[f8215,f3589])).
% 5.22/1.03  fof(f3589,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl2_55),
% 5.22/1.03    inference(avatar_component_clause,[],[f3587])).
% 5.22/1.03  fof(f3587,plain,(
% 5.22/1.03    spl2_55 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 5.22/1.03  fof(f8215,plain,(
% 5.22/1.03    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_48 | ~spl2_54)),
% 5.22/1.03    inference(forward_demodulation,[],[f8065,f3584])).
% 5.22/1.03  fof(f3584,plain,(
% 5.22/1.03    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_54),
% 5.22/1.03    inference(avatar_component_clause,[],[f3582])).
% 5.22/1.03  fof(f3582,plain,(
% 5.22/1.03    spl2_54 <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 5.22/1.03  fof(f8065,plain,(
% 5.22/1.03    k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k7_subset_1(sK1,sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_48),
% 5.22/1.03    inference(resolution,[],[f3097,f496])).
% 5.22/1.03  fof(f496,plain,(
% 5.22/1.03    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k3_subset_1(X2,k3_subset_1(X2,X3)) = k7_subset_1(X2,X2,k3_subset_1(X2,X3))) )),
% 5.22/1.03    inference(backward_demodulation,[],[f206,f447])).
% 5.22/1.03  fof(f206,plain,(
% 5.22/1.03    ( ! [X2,X3] : (k3_subset_1(X2,k3_subset_1(X2,X3)) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k3_subset_1(X2,X3)))) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 5.22/1.03    inference(resolution,[],[f101,f80])).
% 5.22/1.03  fof(f80,plain,(
% 5.22/1.03    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f38])).
% 5.22/1.03  fof(f38,plain,(
% 5.22/1.03    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.22/1.03    inference(ennf_transformation,[],[f16])).
% 5.22/1.03  fof(f16,axiom,(
% 5.22/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 5.22/1.03  fof(f101,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 5.22/1.03    inference(definition_unfolding,[],[f81,f94])).
% 5.22/1.03  fof(f81,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f39])).
% 5.22/1.03  fof(f39,plain,(
% 5.22/1.03    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.22/1.03    inference(ennf_transformation,[],[f15])).
% 5.22/1.03  fof(f15,axiom,(
% 5.22/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 5.22/1.03  fof(f3033,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_3),
% 5.22/1.03    inference(forward_demodulation,[],[f64,f502])).
% 5.22/1.03  fof(f502,plain,(
% 5.22/1.03    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) ) | ~spl2_3),
% 5.22/1.03    inference(backward_demodulation,[],[f244,f447])).
% 5.22/1.03  fof(f244,plain,(
% 5.22/1.03    ( ! [X0] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_3),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f122,f103])).
% 5.22/1.03  fof(f122,plain,(
% 5.22/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 5.22/1.03    inference(avatar_component_clause,[],[f120])).
% 5.22/1.03  fof(f120,plain,(
% 5.22/1.03    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 5.22/1.03  fof(f64,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 5.22/1.03    inference(cnf_transformation,[],[f58])).
% 5.22/1.03  fof(f58,plain,(
% 5.22/1.03    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 5.22/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).
% 5.22/1.03  fof(f56,plain,(
% 5.22/1.03    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 5.22/1.03    introduced(choice_axiom,[])).
% 5.22/1.03  fof(f57,plain,(
% 5.22/1.03    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.22/1.03    introduced(choice_axiom,[])).
% 5.22/1.03  fof(f55,plain,(
% 5.22/1.03    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.22/1.03    inference(flattening,[],[f54])).
% 5.22/1.03  fof(f54,plain,(
% 5.22/1.03    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.22/1.03    inference(nnf_transformation,[],[f32])).
% 5.22/1.03  fof(f32,plain,(
% 5.22/1.03    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.22/1.03    inference(flattening,[],[f31])).
% 5.22/1.03  fof(f31,plain,(
% 5.22/1.03    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 5.22/1.03    inference(ennf_transformation,[],[f30])).
% 5.22/1.03  fof(f30,negated_conjecture,(
% 5.22/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 5.22/1.03    inference(negated_conjecture,[],[f29])).
% 5.22/1.03  fof(f29,conjecture,(
% 5.22/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 5.22/1.03  fof(f4130,plain,(
% 5.22/1.03    spl2_63 | ~spl2_51),
% 5.22/1.03    inference(avatar_split_clause,[],[f3602,f3279,f4127])).
% 5.22/1.03  fof(f3602,plain,(
% 5.22/1.03    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_51),
% 5.22/1.03    inference(superposition,[],[f472,f3281])).
% 5.22/1.03  fof(f472,plain,(
% 5.22/1.03    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) )),
% 5.22/1.03    inference(backward_demodulation,[],[f98,f447])).
% 5.22/1.03  fof(f3976,plain,(
% 5.22/1.03    spl2_47 | ~spl2_45),
% 5.22/1.03    inference(avatar_split_clause,[],[f3527,f3029,f3043])).
% 5.22/1.03  fof(f3029,plain,(
% 5.22/1.03    spl2_45 <=> k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 5.22/1.03  fof(f3527,plain,(
% 5.22/1.03    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_45),
% 5.22/1.03    inference(superposition,[],[f472,f3031])).
% 5.22/1.03  fof(f3031,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~spl2_45),
% 5.22/1.03    inference(avatar_component_clause,[],[f3029])).
% 5.22/1.03  fof(f3600,plain,(
% 5.22/1.03    spl2_56 | ~spl2_3 | ~spl2_16 | ~spl2_47),
% 5.22/1.03    inference(avatar_split_clause,[],[f3087,f3043,f720,f120,f3597])).
% 5.22/1.03  fof(f720,plain,(
% 5.22/1.03    spl2_16 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 5.22/1.03  fof(f3087,plain,(
% 5.22/1.03    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_16 | ~spl2_47)),
% 5.22/1.03    inference(forward_demodulation,[],[f3068,f3083])).
% 5.22/1.03  fof(f3083,plain,(
% 5.22/1.03    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_16 | ~spl2_47)),
% 5.22/1.03    inference(forward_demodulation,[],[f3072,f739])).
% 5.22/1.03  fof(f739,plain,(
% 5.22/1.03    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_16)),
% 5.22/1.03    inference(superposition,[],[f722,f502])).
% 5.22/1.03  fof(f722,plain,(
% 5.22/1.03    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_16),
% 5.22/1.03    inference(avatar_component_clause,[],[f720])).
% 5.22/1.03  fof(f3072,plain,(
% 5.22/1.03    k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_47),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f3045,f484])).
% 5.22/1.03  fof(f484,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 5.22/1.03    inference(backward_demodulation,[],[f205,f447])).
% 5.22/1.03  fof(f205,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X1,X0)) )),
% 5.22/1.03    inference(resolution,[],[f101,f88])).
% 5.22/1.03  fof(f3068,plain,(
% 5.22/1.03    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_47),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f3045,f180])).
% 5.22/1.03  fof(f180,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 5.22/1.03    inference(resolution,[],[f108,f88])).
% 5.22/1.03  fof(f108,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 5.22/1.03    inference(forward_demodulation,[],[f83,f65])).
% 5.22/1.03  fof(f65,plain,(
% 5.22/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 5.22/1.03    inference(cnf_transformation,[],[f14])).
% 5.22/1.03  fof(f14,axiom,(
% 5.22/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 5.22/1.03  fof(f83,plain,(
% 5.22/1.03    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f41])).
% 5.22/1.03  fof(f41,plain,(
% 5.22/1.03    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.22/1.03    inference(ennf_transformation,[],[f20])).
% 5.22/1.03  fof(f20,axiom,(
% 5.22/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 5.22/1.03  fof(f3590,plain,(
% 5.22/1.03    spl2_55 | ~spl2_3 | ~spl2_16 | ~spl2_47),
% 5.22/1.03    inference(avatar_split_clause,[],[f3088,f3043,f720,f120,f3587])).
% 5.22/1.03  fof(f3088,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_16 | ~spl2_47)),
% 5.22/1.03    inference(forward_demodulation,[],[f3067,f3083])).
% 5.22/1.03  fof(f3067,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_47),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f3045,f171])).
% 5.22/1.03  fof(f171,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 5.22/1.03    inference(resolution,[],[f82,f88])).
% 5.22/1.03  fof(f82,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 5.22/1.03    inference(cnf_transformation,[],[f40])).
% 5.22/1.03  fof(f40,plain,(
% 5.22/1.03    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.22/1.03    inference(ennf_transformation,[],[f17])).
% 5.22/1.03  fof(f17,axiom,(
% 5.22/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 5.22/1.03  fof(f3585,plain,(
% 5.22/1.03    spl2_54 | ~spl2_3 | ~spl2_16 | ~spl2_47),
% 5.22/1.03    inference(avatar_split_clause,[],[f3083,f3043,f720,f120,f3582])).
% 5.22/1.03  fof(f3282,plain,(
% 5.22/1.03    spl2_51 | ~spl2_3 | ~spl2_16),
% 5.22/1.03    inference(avatar_split_clause,[],[f739,f720,f120,f3279])).
% 5.22/1.03  fof(f3098,plain,(
% 5.22/1.03    spl2_48 | ~spl2_47),
% 5.22/1.03    inference(avatar_split_clause,[],[f3048,f3043,f3095])).
% 5.22/1.03  fof(f3048,plain,(
% 5.22/1.03    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_47),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f3045,f88])).
% 5.22/1.03  fof(f3046,plain,(
% 5.22/1.03    spl2_47 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 5.22/1.03    inference(avatar_split_clause,[],[f3035,f152,f120,f115,f3043])).
% 5.22/1.03  fof(f115,plain,(
% 5.22/1.03    spl2_2 <=> l1_pre_topc(sK0)),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 5.22/1.03  fof(f152,plain,(
% 5.22/1.03    spl2_5 <=> v4_pre_topc(sK1,sK0)),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 5.22/1.03  fof(f3035,plain,(
% 5.22/1.03    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f117,f122,f154,f71])).
% 5.22/1.03  fof(f71,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 5.22/1.03    inference(cnf_transformation,[],[f37])).
% 5.22/1.03  fof(f37,plain,(
% 5.22/1.03    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.22/1.03    inference(flattening,[],[f36])).
% 5.22/1.03  fof(f36,plain,(
% 5.22/1.03    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.22/1.03    inference(ennf_transformation,[],[f27])).
% 5.22/1.03  fof(f27,axiom,(
% 5.22/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 5.22/1.03  fof(f154,plain,(
% 5.22/1.03    v4_pre_topc(sK1,sK0) | ~spl2_5),
% 5.22/1.03    inference(avatar_component_clause,[],[f152])).
% 5.22/1.03  fof(f117,plain,(
% 5.22/1.03    l1_pre_topc(sK0) | ~spl2_2),
% 5.22/1.03    inference(avatar_component_clause,[],[f115])).
% 5.22/1.03  fof(f3032,plain,(
% 5.22/1.03    spl2_45 | ~spl2_3 | ~spl2_6),
% 5.22/1.03    inference(avatar_split_clause,[],[f646,f156,f120,f3029])).
% 5.22/1.03  fof(f156,plain,(
% 5.22/1.03    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 5.22/1.03  fof(f646,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6)),
% 5.22/1.03    inference(superposition,[],[f502,f158])).
% 5.22/1.03  fof(f158,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 5.22/1.03    inference(avatar_component_clause,[],[f156])).
% 5.22/1.03  fof(f3027,plain,(
% 5.22/1.03    spl2_44 | ~spl2_2 | ~spl2_3 | ~spl2_8),
% 5.22/1.03    inference(avatar_split_clause,[],[f323,f298,f120,f115,f3024])).
% 5.22/1.03  fof(f298,plain,(
% 5.22/1.03    spl2_8 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 5.22/1.03  fof(f323,plain,(
% 5.22/1.03    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_3 | ~spl2_8)),
% 5.22/1.03    inference(forward_demodulation,[],[f314,f295])).
% 5.22/1.03  fof(f295,plain,(
% 5.22/1.03    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f117,f122,f70])).
% 5.22/1.03  fof(f70,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f35])).
% 5.22/1.03  fof(f35,plain,(
% 5.22/1.03    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.22/1.03    inference(ennf_transformation,[],[f26])).
% 5.22/1.03  fof(f26,axiom,(
% 5.22/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 5.22/1.03  fof(f314,plain,(
% 5.22/1.03    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_8)),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f122,f300,f106])).
% 5.22/1.03  fof(f300,plain,(
% 5.22/1.03    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_8),
% 5.22/1.03    inference(avatar_component_clause,[],[f298])).
% 5.22/1.03  fof(f723,plain,(
% 5.22/1.03    spl2_16 | ~spl2_2 | ~spl2_3),
% 5.22/1.03    inference(avatar_split_clause,[],[f273,f120,f115,f720])).
% 5.22/1.03  fof(f273,plain,(
% 5.22/1.03    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f117,f122,f69])).
% 5.22/1.03  fof(f69,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 5.22/1.03    inference(cnf_transformation,[],[f34])).
% 5.22/1.03  fof(f34,plain,(
% 5.22/1.03    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 5.22/1.03    inference(ennf_transformation,[],[f28])).
% 5.22/1.03  fof(f28,axiom,(
% 5.22/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 5.22/1.03  fof(f301,plain,(
% 5.22/1.03    spl2_8 | ~spl2_2 | ~spl2_3),
% 5.22/1.03    inference(avatar_split_clause,[],[f195,f120,f115,f298])).
% 5.22/1.03  fof(f195,plain,(
% 5.22/1.03    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f117,f122,f86])).
% 5.22/1.03  fof(f86,plain,(
% 5.22/1.03    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 5.22/1.03    inference(cnf_transformation,[],[f46])).
% 5.22/1.03  fof(f46,plain,(
% 5.22/1.03    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 5.22/1.03    inference(flattening,[],[f45])).
% 5.22/1.03  fof(f45,plain,(
% 5.22/1.03    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 5.22/1.03    inference(ennf_transformation,[],[f23])).
% 5.22/1.03  fof(f23,axiom,(
% 5.22/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 5.22/1.03  fof(f215,plain,(
% 5.22/1.03    spl2_7 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 5.22/1.03    inference(avatar_split_clause,[],[f192,f120,f115,f110,f212])).
% 5.22/1.03  fof(f110,plain,(
% 5.22/1.03    spl2_1 <=> v2_pre_topc(sK0)),
% 5.22/1.03    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 5.22/1.03  fof(f192,plain,(
% 5.22/1.03    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 5.22/1.03    inference(unit_resulting_resolution,[],[f112,f117,f122,f85])).
% 5.22/1.03  fof(f85,plain,(
% 5.22/1.03    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 5.22/1.03    inference(cnf_transformation,[],[f44])).
% 5.22/1.03  fof(f44,plain,(
% 5.22/1.03    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.22/1.03    inference(flattening,[],[f43])).
% 5.22/1.03  fof(f43,plain,(
% 5.22/1.03    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.22/1.03    inference(ennf_transformation,[],[f24])).
% 5.22/1.03  fof(f24,axiom,(
% 5.22/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 5.22/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 5.22/1.03  fof(f112,plain,(
% 5.22/1.03    v2_pre_topc(sK0) | ~spl2_1),
% 5.22/1.03    inference(avatar_component_clause,[],[f110])).
% 5.22/1.03  fof(f159,plain,(
% 5.22/1.03    spl2_5 | spl2_6),
% 5.22/1.03    inference(avatar_split_clause,[],[f63,f156,f152])).
% 5.22/1.03  fof(f63,plain,(
% 5.22/1.03    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 5.22/1.03    inference(cnf_transformation,[],[f58])).
% 5.22/1.03  fof(f123,plain,(
% 5.22/1.03    spl2_3),
% 5.22/1.03    inference(avatar_split_clause,[],[f62,f120])).
% 5.22/1.03  fof(f62,plain,(
% 5.22/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 5.22/1.03    inference(cnf_transformation,[],[f58])).
% 5.22/1.03  fof(f118,plain,(
% 5.22/1.03    spl2_2),
% 5.22/1.03    inference(avatar_split_clause,[],[f61,f115])).
% 5.22/1.03  fof(f61,plain,(
% 5.22/1.03    l1_pre_topc(sK0)),
% 5.22/1.03    inference(cnf_transformation,[],[f58])).
% 5.22/1.03  fof(f113,plain,(
% 5.22/1.03    spl2_1),
% 5.22/1.03    inference(avatar_split_clause,[],[f60,f110])).
% 5.22/1.03  fof(f60,plain,(
% 5.22/1.03    v2_pre_topc(sK0)),
% 5.22/1.03    inference(cnf_transformation,[],[f58])).
% 5.22/1.03  % SZS output end Proof for theBenchmark
% 5.22/1.03  % (7231)------------------------------
% 5.22/1.03  % (7231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.22/1.03  % (7231)Termination reason: Refutation
% 5.22/1.03  
% 5.22/1.03  % (7231)Memory used [KB]: 18549
% 5.22/1.03  % (7231)Time elapsed: 0.544 s
% 5.22/1.03  % (7231)------------------------------
% 5.22/1.03  % (7231)------------------------------
% 5.22/1.03  % (7215)Success in time 0.667 s
%------------------------------------------------------------------------------
