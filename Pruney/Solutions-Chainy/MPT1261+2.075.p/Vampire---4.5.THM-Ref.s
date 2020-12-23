%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:59 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 696 expanded)
%              Number of leaves         :   26 ( 252 expanded)
%              Depth                    :   18
%              Number of atoms          :  308 (1257 expanded)
%              Number of equality atoms :  106 ( 716 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f904,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f72,f127,f129,f131,f516,f525,f682,f684,f901,f903])).

fof(f903,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | spl2_11 ),
    inference(avatar_split_clause,[],[f902,f896,f509,f116])).

fof(f116,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f509,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f896,plain,
    ( spl2_11
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f902,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_11 ),
    inference(resolution,[],[f898,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f898,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f896])).

fof(f901,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11
    | spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f894,f513,f124,f896,f509,f116])).

fof(f124,plain,
    ( spl2_5
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f513,plain,
    ( spl2_7
  <=> sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f894,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_7 ),
    inference(superposition,[],[f567,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f62,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f567,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_7 ),
    inference(superposition,[],[f229,f530])).

fof(f530,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f527,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f527,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_7 ),
    inference(superposition,[],[f280,f515])).

fof(f515,plain,
    ( sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f513])).

fof(f280,plain,(
    ! [X4,X3] : k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X3,X4)))) = X3 ),
    inference(superposition,[],[f84,f107])).

fof(f107,plain,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f96,f46])).

fof(f96,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f79,f95])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f93,f57])).

fof(f57,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) ),
    inference(superposition,[],[f58,f79])).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) ),
    inference(definition_unfolding,[],[f47,f56,f48])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f79,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k5_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[],[f59,f57])).

fof(f59,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f51,f48,f49,f56])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f84,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_xboole_0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))) = X0 ),
    inference(forward_demodulation,[],[f80,f46])).

fof(f80,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k1_xboole_0)) = X0 ),
    inference(superposition,[],[f59,f58])).

fof(f229,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f228,f186])).

fof(f186,plain,(
    ! [X1] : k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 ),
    inference(forward_demodulation,[],[f185,f59])).

fof(f185,plain,(
    ! [X0,X1] : k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(forward_demodulation,[],[f184,f46])).

fof(f184,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))),k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f158,f95])).

fof(f158,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))),k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,X0)))) ),
    inference(superposition,[],[f60,f57])).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X2)))) ),
    inference(definition_unfolding,[],[f53,f56,f56,f48,f56,f49])).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f228,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(forward_demodulation,[],[f227,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f227,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f221,f191])).

fof(f191,plain,(
    ! [X15] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X15)) ),
    inference(forward_demodulation,[],[f190,f109])).

fof(f109,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
    inference(superposition,[],[f73,f96])).

fof(f73,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))) ),
    inference(superposition,[],[f58,f46])).

fof(f190,plain,(
    ! [X14,X15] : k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(X14,k1_setfam_1(k2_tarski(X14,X15)))))) = k1_setfam_1(k2_tarski(k1_xboole_0,X15)) ),
    inference(forward_demodulation,[],[f172,f107])).

fof(f172,plain,(
    ! [X14,X15] : k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(X14,k1_setfam_1(k2_tarski(X14,X15)))))) = k3_tarski(k2_tarski(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X15)))) ),
    inference(superposition,[],[f60,f109])).

fof(f221,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))))) = k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(superposition,[],[f60,f186])).

fof(f684,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f683,f124,f68,f509,f116])).

fof(f68,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f683,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(superposition,[],[f42,f125])).

fof(f125,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f682,plain,
    ( ~ spl2_3
    | spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f88,f64,f124,f116])).

fof(f64,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f88,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f32,plain,
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

fof(f33,plain,
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

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f525,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f511,f37])).

fof(f511,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f509])).

fof(f516,plain,
    ( ~ spl2_6
    | spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f507,f68,f513,f509])).

fof(f507,plain,
    ( sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f486,f46])).

fof(f486,plain,
    ( sK1 = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))),k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f105,f69])).

fof(f69,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f105,plain,(
    ! [X6,X8,X7] :
      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X6,X7)),k7_subset_1(X8,X6,X7))) = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(X8)) ) ),
    inference(superposition,[],[f59,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f56])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f131,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f122,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f122,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl2_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f129,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f118,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f127,plain,
    ( ~ spl2_3
    | spl2_1
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f112,f124,f120,f64,f116])).

fof(f112,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f37])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f38,f68,f64])).

fof(f38,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f39,f68,f64])).

fof(f39,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:50:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (10170)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (10173)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (10183)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (10175)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (10172)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (10178)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (10169)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (10180)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (10182)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (10185)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (10179)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (10168)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (10181)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (10171)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (10177)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (10176)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (10184)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (10174)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.23/0.52  % (10172)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % SZS output start Proof for theBenchmark
% 1.23/0.52  fof(f904,plain,(
% 1.23/0.52    $false),
% 1.23/0.52    inference(avatar_sat_refutation,[],[f71,f72,f127,f129,f131,f516,f525,f682,f684,f901,f903])).
% 1.23/0.52  fof(f903,plain,(
% 1.23/0.52    ~spl2_3 | ~spl2_6 | spl2_11),
% 1.23/0.52    inference(avatar_split_clause,[],[f902,f896,f509,f116])).
% 1.23/0.52  fof(f116,plain,(
% 1.23/0.52    spl2_3 <=> l1_pre_topc(sK0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.23/0.52  fof(f509,plain,(
% 1.23/0.52    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.23/0.52  fof(f896,plain,(
% 1.23/0.52    spl2_11 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.23/0.52  fof(f902,plain,(
% 1.23/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_11),
% 1.23/0.52    inference(resolution,[],[f898,f52])).
% 1.23/0.52  fof(f52,plain,(
% 1.23/0.52    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f26])).
% 1.23/0.52  fof(f26,plain,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(flattening,[],[f25])).
% 1.23/0.52  fof(f25,plain,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f13])).
% 1.23/0.52  fof(f13,axiom,(
% 1.23/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.23/0.52  fof(f898,plain,(
% 1.23/0.52    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_11),
% 1.23/0.52    inference(avatar_component_clause,[],[f896])).
% 1.23/0.52  fof(f901,plain,(
% 1.23/0.52    ~spl2_3 | ~spl2_6 | ~spl2_11 | spl2_5 | ~spl2_7),
% 1.23/0.52    inference(avatar_split_clause,[],[f894,f513,f124,f896,f509,f116])).
% 1.23/0.52  fof(f124,plain,(
% 1.23/0.52    spl2_5 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.23/0.52  fof(f513,plain,(
% 1.23/0.52    spl2_7 <=> sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.23/0.52  fof(f894,plain,(
% 1.23/0.52    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_7),
% 1.23/0.52    inference(superposition,[],[f567,f139])).
% 1.23/0.52  fof(f139,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f138])).
% 1.23/0.52  fof(f138,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(superposition,[],[f62,f41])).
% 1.23/0.52  fof(f41,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f21])).
% 1.23/0.52  fof(f21,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f15])).
% 1.23/0.52  fof(f15,axiom,(
% 1.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.23/0.52  fof(f62,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.23/0.52    inference(definition_unfolding,[],[f55,f48])).
% 1.23/0.52  fof(f48,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f8])).
% 1.23/0.52  fof(f8,axiom,(
% 1.23/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.23/0.52  fof(f55,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f29])).
% 1.23/0.52  fof(f29,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.23/0.52    inference(flattening,[],[f28])).
% 1.23/0.52  fof(f28,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.23/0.52    inference(ennf_transformation,[],[f9])).
% 1.23/0.52  fof(f9,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.23/0.52  fof(f567,plain,(
% 1.23/0.52    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_7),
% 1.23/0.52    inference(superposition,[],[f229,f530])).
% 1.23/0.52  fof(f530,plain,(
% 1.23/0.52    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_7),
% 1.23/0.52    inference(forward_demodulation,[],[f527,f46])).
% 1.23/0.52  fof(f46,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f7])).
% 1.23/0.52  fof(f7,axiom,(
% 1.23/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.23/0.52  fof(f527,plain,(
% 1.23/0.52    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | ~spl2_7),
% 1.23/0.52    inference(superposition,[],[f280,f515])).
% 1.23/0.52  fof(f515,plain,(
% 1.23/0.52    sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))) | ~spl2_7),
% 1.23/0.52    inference(avatar_component_clause,[],[f513])).
% 1.23/0.52  fof(f280,plain,(
% 1.23/0.52    ( ! [X4,X3] : (k1_setfam_1(k2_tarski(X3,k3_tarski(k2_tarski(X3,X4)))) = X3) )),
% 1.23/0.52    inference(superposition,[],[f84,f107])).
% 1.23/0.52  fof(f107,plain,(
% 1.23/0.52    ( ! [X0] : (k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0) )),
% 1.23/0.52    inference(superposition,[],[f96,f46])).
% 1.23/0.52  fof(f96,plain,(
% 1.23/0.52    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 1.23/0.52    inference(backward_demodulation,[],[f79,f95])).
% 1.23/0.52  fof(f95,plain,(
% 1.23/0.52    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.23/0.52    inference(forward_demodulation,[],[f93,f57])).
% 1.23/0.52  fof(f57,plain,(
% 1.23/0.52    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.23/0.52    inference(definition_unfolding,[],[f45,f49])).
% 1.23/0.52  fof(f49,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f11])).
% 1.23/0.52  fof(f11,axiom,(
% 1.23/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.23/0.52  fof(f45,plain,(
% 1.23/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f18])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.23/0.52    inference(rectify,[],[f1])).
% 1.23/0.52  fof(f1,axiom,(
% 1.23/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.23/0.52  fof(f93,plain,(
% 1.23/0.52    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))) )),
% 1.23/0.52    inference(superposition,[],[f58,f79])).
% 1.23/0.52  fof(f58,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))) )),
% 1.23/0.52    inference(definition_unfolding,[],[f47,f56,f48])).
% 1.23/0.52  fof(f56,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.23/0.52    inference(definition_unfolding,[],[f50,f49])).
% 1.23/0.52  fof(f50,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f2])).
% 1.23/0.52  fof(f2,axiom,(
% 1.23/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.23/0.52  fof(f47,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f3])).
% 1.23/0.52  fof(f3,axiom,(
% 1.23/0.52    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.23/0.52  fof(f79,plain,(
% 1.23/0.52    ( ! [X0] : (k3_tarski(k2_tarski(X0,k5_xboole_0(X0,X0))) = X0) )),
% 1.23/0.52    inference(superposition,[],[f59,f57])).
% 1.23/0.52  fof(f59,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) )),
% 1.23/0.52    inference(definition_unfolding,[],[f51,f48,f49,f56])).
% 1.23/0.52  fof(f51,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f4])).
% 1.23/0.52  fof(f4,axiom,(
% 1.23/0.52    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.23/0.52  fof(f84,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_xboole_0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))) = X0) )),
% 1.23/0.52    inference(forward_demodulation,[],[f80,f46])).
% 1.23/0.52  fof(f80,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k1_xboole_0)) = X0) )),
% 1.23/0.52    inference(superposition,[],[f59,f58])).
% 1.23/0.52  fof(f229,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 1.23/0.52    inference(forward_demodulation,[],[f228,f186])).
% 1.23/0.52  fof(f186,plain,(
% 1.23/0.52    ( ! [X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1) )),
% 1.23/0.52    inference(forward_demodulation,[],[f185,f59])).
% 1.23/0.52  fof(f185,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f184,f46])).
% 1.23/0.52  fof(f184,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))),k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0)))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f158,f95])).
% 1.23/0.52  fof(f158,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))),k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,X0))))) )),
% 1.23/0.52    inference(superposition,[],[f60,f57])).
% 1.23/0.52  fof(f60,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))))) = k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X2))))) )),
% 1.23/0.52    inference(definition_unfolding,[],[f53,f56,f56,f48,f56,f49])).
% 1.23/0.52  fof(f53,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f5])).
% 1.23/0.52  fof(f5,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.23/0.52  fof(f228,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f227,f40])).
% 1.23/0.52  fof(f40,plain,(
% 1.23/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f6])).
% 1.23/0.52  fof(f6,axiom,(
% 1.23/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.23/0.52  fof(f227,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f221,f191])).
% 1.23/0.52  fof(f191,plain,(
% 1.23/0.52    ( ! [X15] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X15))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f190,f109])).
% 1.23/0.52  fof(f109,plain,(
% 1.23/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) )),
% 1.23/0.52    inference(superposition,[],[f73,f96])).
% 1.23/0.52  fof(f73,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))))) )),
% 1.23/0.52    inference(superposition,[],[f58,f46])).
% 1.23/0.52  fof(f190,plain,(
% 1.23/0.52    ( ! [X14,X15] : (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(X14,k1_setfam_1(k2_tarski(X14,X15)))))) = k1_setfam_1(k2_tarski(k1_xboole_0,X15))) )),
% 1.23/0.52    inference(forward_demodulation,[],[f172,f107])).
% 1.23/0.52  fof(f172,plain,(
% 1.23/0.52    ( ! [X14,X15] : (k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(X14,k1_setfam_1(k2_tarski(X14,X15)))))) = k3_tarski(k2_tarski(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X15))))) )),
% 1.23/0.52    inference(superposition,[],[f60,f109])).
% 1.23/0.52  fof(f221,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X1)))))) = k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 1.23/0.52    inference(superposition,[],[f60,f186])).
% 1.23/0.52  fof(f684,plain,(
% 1.23/0.52    ~spl2_3 | ~spl2_6 | spl2_2 | ~spl2_5),
% 1.23/0.52    inference(avatar_split_clause,[],[f683,f124,f68,f509,f116])).
% 1.23/0.52  fof(f68,plain,(
% 1.23/0.52    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.23/0.52  fof(f683,plain,(
% 1.23/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_5),
% 1.23/0.52    inference(superposition,[],[f42,f125])).
% 1.23/0.52  fof(f125,plain,(
% 1.23/0.52    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_5),
% 1.23/0.52    inference(avatar_component_clause,[],[f124])).
% 1.23/0.52  fof(f42,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f22])).
% 1.23/0.52  fof(f22,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f14])).
% 1.23/0.52  fof(f14,axiom,(
% 1.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.23/0.52  fof(f682,plain,(
% 1.23/0.52    ~spl2_3 | spl2_5 | ~spl2_1),
% 1.23/0.52    inference(avatar_split_clause,[],[f88,f64,f124,f116])).
% 1.23/0.52  fof(f64,plain,(
% 1.23/0.52    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.23/0.52  fof(f88,plain,(
% 1.23/0.52    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.23/0.52    inference(resolution,[],[f43,f37])).
% 1.23/0.52  fof(f37,plain,(
% 1.23/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.23/0.52    inference(cnf_transformation,[],[f34])).
% 1.23/0.52  fof(f34,plain,(
% 1.23/0.52    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 1.23/0.52  fof(f32,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f33,plain,(
% 1.23/0.52    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f31,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.23/0.52    inference(flattening,[],[f30])).
% 1.23/0.52  fof(f30,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.23/0.52    inference(nnf_transformation,[],[f20])).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.23/0.52    inference(flattening,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f17])).
% 1.23/0.52  fof(f17,negated_conjecture,(
% 1.23/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.23/0.52    inference(negated_conjecture,[],[f16])).
% 1.23/0.52  fof(f16,conjecture,(
% 1.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.23/0.52  fof(f43,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f24])).
% 1.23/0.52  fof(f24,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(flattening,[],[f23])).
% 1.23/0.52  fof(f23,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f12])).
% 1.23/0.52  fof(f12,axiom,(
% 1.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.23/0.52  fof(f525,plain,(
% 1.23/0.52    spl2_6),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f524])).
% 1.23/0.52  fof(f524,plain,(
% 1.23/0.52    $false | spl2_6),
% 1.23/0.52    inference(resolution,[],[f511,f37])).
% 1.23/0.52  fof(f511,plain,(
% 1.23/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_6),
% 1.23/0.52    inference(avatar_component_clause,[],[f509])).
% 1.23/0.52  fof(f516,plain,(
% 1.23/0.52    ~spl2_6 | spl2_7 | ~spl2_2),
% 1.23/0.52    inference(avatar_split_clause,[],[f507,f68,f513,f509])).
% 1.23/0.52  fof(f507,plain,(
% 1.23/0.52    sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.23/0.52    inference(forward_demodulation,[],[f486,f46])).
% 1.23/0.52  fof(f486,plain,(
% 1.23/0.52    sK1 = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))),k2_tops_1(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.23/0.52    inference(superposition,[],[f105,f69])).
% 1.23/0.52  fof(f69,plain,(
% 1.23/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 1.23/0.52    inference(avatar_component_clause,[],[f68])).
% 1.23/0.52  fof(f105,plain,(
% 1.23/0.52    ( ! [X6,X8,X7] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X6,X7)),k7_subset_1(X8,X6,X7))) = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X8))) )),
% 1.23/0.52    inference(superposition,[],[f59,f61])).
% 1.23/0.52  fof(f61,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.23/0.52    inference(definition_unfolding,[],[f54,f56])).
% 1.23/0.52  fof(f54,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f27])).
% 1.23/0.52  fof(f27,plain,(
% 1.23/0.52    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f10])).
% 1.23/0.52  fof(f10,axiom,(
% 1.23/0.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.23/0.52  fof(f131,plain,(
% 1.23/0.52    spl2_4),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f130])).
% 1.23/0.52  fof(f130,plain,(
% 1.23/0.52    $false | spl2_4),
% 1.23/0.52    inference(resolution,[],[f122,f35])).
% 1.23/0.52  fof(f35,plain,(
% 1.23/0.52    v2_pre_topc(sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f34])).
% 1.23/0.52  fof(f122,plain,(
% 1.23/0.52    ~v2_pre_topc(sK0) | spl2_4),
% 1.23/0.52    inference(avatar_component_clause,[],[f120])).
% 1.23/0.52  fof(f120,plain,(
% 1.23/0.52    spl2_4 <=> v2_pre_topc(sK0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.23/0.52  fof(f129,plain,(
% 1.23/0.52    spl2_3),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f128])).
% 1.23/0.52  fof(f128,plain,(
% 1.23/0.52    $false | spl2_3),
% 1.23/0.52    inference(resolution,[],[f118,f36])).
% 1.23/0.52  fof(f36,plain,(
% 1.23/0.52    l1_pre_topc(sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f34])).
% 1.23/0.52  fof(f118,plain,(
% 1.23/0.52    ~l1_pre_topc(sK0) | spl2_3),
% 1.23/0.52    inference(avatar_component_clause,[],[f116])).
% 1.23/0.52  fof(f127,plain,(
% 1.23/0.52    ~spl2_3 | spl2_1 | ~spl2_4 | ~spl2_5),
% 1.23/0.52    inference(avatar_split_clause,[],[f112,f124,f120,f64,f116])).
% 1.23/0.52  fof(f112,plain,(
% 1.23/0.52    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.23/0.52    inference(resolution,[],[f44,f37])).
% 1.23/0.52  fof(f44,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f24])).
% 1.23/0.52  fof(f72,plain,(
% 1.23/0.52    spl2_1 | spl2_2),
% 1.23/0.52    inference(avatar_split_clause,[],[f38,f68,f64])).
% 1.23/0.52  fof(f38,plain,(
% 1.23/0.52    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f34])).
% 1.23/0.52  fof(f71,plain,(
% 1.23/0.52    ~spl2_1 | ~spl2_2),
% 1.23/0.52    inference(avatar_split_clause,[],[f39,f68,f64])).
% 1.23/0.52  fof(f39,plain,(
% 1.23/0.52    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.23/0.52    inference(cnf_transformation,[],[f34])).
% 1.23/0.52  % SZS output end Proof for theBenchmark
% 1.23/0.52  % (10172)------------------------------
% 1.23/0.52  % (10172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (10172)Termination reason: Refutation
% 1.23/0.52  
% 1.23/0.52  % (10172)Memory used [KB]: 6524
% 1.23/0.52  % (10172)Time elapsed: 0.086 s
% 1.23/0.52  % (10172)------------------------------
% 1.23/0.52  % (10172)------------------------------
% 1.23/0.52  % (10167)Success in time 0.159 s
%------------------------------------------------------------------------------
