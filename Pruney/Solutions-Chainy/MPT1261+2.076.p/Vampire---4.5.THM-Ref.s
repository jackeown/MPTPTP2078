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
% DateTime   : Thu Dec  3 13:11:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 408 expanded)
%              Number of leaves         :   42 ( 168 expanded)
%              Depth                    :   11
%              Number of atoms          :  467 (1043 expanded)
%              Number of equality atoms :  143 ( 377 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1781,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f93,f94,f100,f134,f190,f203,f208,f213,f279,f289,f309,f328,f335,f348,f349,f866,f893,f948,f1090,f1096,f1137,f1768])).

fof(f1768,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | spl2_42
    | ~ spl2_45
    | ~ spl2_54 ),
    inference(avatar_contradiction_clause,[],[f1767])).

fof(f1767,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_6
    | spl2_42
    | ~ spl2_45
    | ~ spl2_54 ),
    inference(global_subsumption,[],[f860,f1734])).

fof(f1734,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_45
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f1733,f65])).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f59,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f48])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1733,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_45
    | ~ spl2_54 ),
    inference(forward_demodulation,[],[f1732,f1136])).

fof(f1136,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1134,plain,
    ( spl2_54
  <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f1732,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f1599,f892])).

fof(f892,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0)))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f891])).

fof(f891,plain,
    ( spl2_45
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f1599,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1))))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f79,f99,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) ) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

% (22744)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

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

fof(f99,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_6
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f860,plain,
    ( sK1 != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | spl2_42 ),
    inference(avatar_component_clause,[],[f859])).

fof(f859,plain,
    ( spl2_42
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f1137,plain,
    ( spl2_54
    | ~ spl2_26
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f1126,f946,f345,f1134])).

fof(f345,plain,
    ( spl2_26
  <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f946,plain,
    ( spl2_48
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f1126,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_26
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f1106,f179])).

fof(f179,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f178,f60])).

fof(f60,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f178,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) ),
    inference(forward_demodulation,[],[f169,f65])).

fof(f169,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_xboole_0)))) ),
    inference(superposition,[],[f61,f58])).

fof(f61,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f50,f48,f56,f56])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1106,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_26
    | ~ spl2_48 ),
    inference(superposition,[],[f947,f347])).

fof(f347,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f345])).

fof(f947,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f946])).

fof(f1096,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_42
    | ~ spl2_43 ),
    inference(avatar_contradiction_clause,[],[f1095])).

fof(f1095,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_42
    | ~ spl2_43 ),
    inference(global_subsumption,[],[f883,f1094])).

fof(f1094,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f74,f69,f79,f87,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
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

fof(f87,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f69,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f74,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f883,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_42
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f874,f861])).

fof(f861,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f859])).

fof(f874,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_43 ),
    inference(resolution,[],[f865,f79])).

fof(f865,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl2_43
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f1090,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_25 ),
    inference(avatar_contradiction_clause,[],[f1089])).

fof(f1089,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_25 ),
    inference(global_subsumption,[],[f91,f1086])).

fof(f1086,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f1077,f334])).

fof(f334,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl2_25
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f1077,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f74,f79,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
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

fof(f91,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f90])).

% (22740)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f90,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f948,plain,
    ( spl2_48
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f894,f891,f946])).

fof(f894,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))))
    | ~ spl2_45 ),
    inference(superposition,[],[f892,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f893,plain,
    ( spl2_45
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f121,f97,f891])).

fof(f121,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0)))
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f99,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f54,f56])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f866,plain,
    ( spl2_43
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f856,f72,f864])).

fof(f856,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f42,f74])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
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

fof(f349,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) != k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f348,plain,
    ( spl2_26
    | ~ spl2_21
    | ~ spl2_23
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f342,f325,f311,f287,f345])).

fof(f287,plain,
    ( spl2_21
  <=> ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f311,plain,
    ( spl2_23
  <=> k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f325,plain,
    ( spl2_24
  <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f342,plain,
    ( k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_21
    | ~ spl2_23
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f340,f327])).

fof(f327,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f325])).

fof(f340,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_21
    | ~ spl2_23 ),
    inference(superposition,[],[f288,f313])).

fof(f313,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f311])).

fof(f288,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f287])).

fof(f335,plain,
    ( spl2_25
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f329,f86,f77,f72,f332])).

fof(f329,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f74,f79,f88,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f328,plain,
    ( spl2_24
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f322,f306,f132,f90,f325])).

fof(f132,plain,
    ( spl2_10
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f306,plain,
    ( spl2_22
  <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f322,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f316,f92])).

fof(f92,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f316,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(superposition,[],[f133,f308])).

fof(f308,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f306])).

fof(f133,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f309,plain,
    ( spl2_22
    | ~ spl2_5
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f294,f287,f90,f306])).

fof(f294,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_21 ),
    inference(superposition,[],[f288,f92])).

fof(f289,plain,
    ( spl2_21
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f282,f277,f211,f287])).

fof(f211,plain,
    ( spl2_18
  <=> ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f277,plain,
    ( spl2_20
  <=> ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f282,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))
    | ~ spl2_18
    | ~ spl2_20 ),
    inference(superposition,[],[f212,f278])).

fof(f278,plain,
    ( ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f277])).

fof(f212,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2))))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f279,plain,
    ( spl2_20
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f245,f132,f277])).

fof(f245,plain,
    ( ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2)))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f238,f133])).

fof(f238,plain,
    ( ! [X2] : k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X2))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2)))
    | ~ spl2_10 ),
    inference(superposition,[],[f62,f133])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))))) ),
    inference(definition_unfolding,[],[f52,f56,f56,f48])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f213,plain,
    ( spl2_18
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f209,f206,f188,f211])).

fof(f188,plain,
    ( spl2_15
  <=> ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f206,plain,
    ( spl2_17
  <=> ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f209,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2))))
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f207,f192])).

fof(f192,plain,
    ( ! [X0] : k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_15 ),
    inference(superposition,[],[f189,f189])).

fof(f189,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f207,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f206])).

fof(f208,plain,
    ( spl2_17
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f173,f132,f206])).

fof(f173,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))))
    | ~ spl2_10 ),
    inference(superposition,[],[f61,f133])).

fof(f203,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f193,f188,f90,f200])).

fof(f200,plain,
    ( spl2_16
  <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f193,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(superposition,[],[f189,f92])).

fof(f190,plain,
    ( spl2_15
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f185,f132,f188])).

fof(f185,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f176,f133])).

fof(f176,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X2))))
    | ~ spl2_10 ),
    inference(superposition,[],[f61,f133])).

fof(f134,plain,
    ( spl2_10
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f120,f77,f132])).

fof(f120,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f79,f63])).

fof(f100,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f95,f77,f72,f97])).

fof(f95,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f74,f79,f53])).

fof(f53,plain,(
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

fof(f94,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f39,f90,f86])).

fof(f39,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
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

fof(f93,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f38,f90,f86])).

fof(f38,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f36,f72])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:20:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (22751)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.46  % (22736)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (22747)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (22749)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (22743)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (22746)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (22735)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (22745)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (22742)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (22738)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (22751)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f1781,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f70,f75,f80,f93,f94,f100,f134,f190,f203,f208,f213,f279,f289,f309,f328,f335,f348,f349,f866,f893,f948,f1090,f1096,f1137,f1768])).
% 0.22/0.50  fof(f1768,plain,(
% 0.22/0.50    ~spl2_3 | ~spl2_6 | spl2_42 | ~spl2_45 | ~spl2_54),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f1767])).
% 0.22/0.50  fof(f1767,plain,(
% 0.22/0.50    $false | (~spl2_3 | ~spl2_6 | spl2_42 | ~spl2_45 | ~spl2_54)),
% 0.22/0.50    inference(global_subsumption,[],[f860,f1734])).
% 0.22/0.50  fof(f1734,plain,(
% 0.22/0.50    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6 | ~spl2_45 | ~spl2_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f1733,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(forward_demodulation,[],[f59,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f40,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 0.22/0.50    inference(definition_unfolding,[],[f41,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f51,f48])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.50  fof(f1733,plain,(
% 0.22/0.50    k5_xboole_0(sK1,k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_6 | ~spl2_45 | ~spl2_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f1732,f1136])).
% 0.22/0.50  fof(f1136,plain,(
% 0.22/0.50    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | ~spl2_54),
% 0.22/0.50    inference(avatar_component_clause,[],[f1134])).
% 0.22/0.50  fof(f1134,plain,(
% 0.22/0.50    spl2_54 <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.22/0.50  fof(f1732,plain,(
% 0.22/0.50    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)) | (~spl2_3 | ~spl2_6 | ~spl2_45)),
% 0.22/0.50    inference(forward_demodulation,[],[f1599,f892])).
% 0.22/0.50  fof(f892,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0)))) ) | ~spl2_45),
% 0.22/0.50    inference(avatar_component_clause,[],[f891])).
% 0.22/0.50  fof(f891,plain,(
% 0.22/0.50    spl2_45 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.22/0.50  fof(f1599,plain,(
% 0.22/0.50    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)))) | (~spl2_3 | ~spl2_6)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f79,f99,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f55,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f49,f56])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  % (22744)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl2_6 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f860,plain,(
% 0.22/0.50    sK1 != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | spl2_42),
% 0.22/0.50    inference(avatar_component_clause,[],[f859])).
% 0.22/0.50  fof(f859,plain,(
% 0.22/0.50    spl2_42 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.22/0.50  fof(f1137,plain,(
% 0.22/0.50    spl2_54 | ~spl2_26 | ~spl2_48),
% 0.22/0.50    inference(avatar_split_clause,[],[f1126,f946,f345,f1134])).
% 0.22/0.50  fof(f345,plain,(
% 0.22/0.50    spl2_26 <=> k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.50  fof(f946,plain,(
% 0.22/0.50    spl2_48 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 0.22/0.50  fof(f1126,plain,(
% 0.22/0.50    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | (~spl2_26 | ~spl2_48)),
% 0.22/0.50    inference(forward_demodulation,[],[f1106,f179])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f178,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 0.22/0.50    inference(definition_unfolding,[],[f46,f48])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.50    inference(rectify,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f169,f65])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_xboole_0))))) )),
% 0.22/0.50    inference(superposition,[],[f61,f58])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f50,f48,f56,f56])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f1106,plain,(
% 0.22/0.50    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) | (~spl2_26 | ~spl2_48)),
% 0.22/0.50    inference(superposition,[],[f947,f347])).
% 0.22/0.50  fof(f347,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f345])).
% 0.22/0.50  fof(f947,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))))) ) | ~spl2_48),
% 0.22/0.50    inference(avatar_component_clause,[],[f946])).
% 0.22/0.50  fof(f1096,plain,(
% 0.22/0.50    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_42 | ~spl2_43),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f1095])).
% 0.22/0.50  fof(f1095,plain,(
% 0.22/0.50    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_42 | ~spl2_43)),
% 0.22/0.50    inference(global_subsumption,[],[f883,f1094])).
% 0.22/0.50  fof(f1094,plain,(
% 0.22/0.50    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f74,f69,f79,f87,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    v2_pre_topc(sK0) | ~spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl2_1 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl2_2 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f883,plain,(
% 0.22/0.50    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_42 | ~spl2_43)),
% 0.22/0.50    inference(forward_demodulation,[],[f874,f861])).
% 0.22/0.50  fof(f861,plain,(
% 0.22/0.50    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_42),
% 0.22/0.50    inference(avatar_component_clause,[],[f859])).
% 0.22/0.50  fof(f874,plain,(
% 0.22/0.50    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_43)),
% 0.22/0.50    inference(resolution,[],[f865,f79])).
% 0.22/0.50  fof(f865,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_43),
% 0.22/0.50    inference(avatar_component_clause,[],[f864])).
% 0.22/0.50  fof(f864,plain,(
% 0.22/0.50    spl2_43 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.22/0.50  fof(f1090,plain,(
% 0.22/0.50    ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_25),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f1089])).
% 0.22/0.50  fof(f1089,plain,(
% 0.22/0.50    $false | (~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_25)),
% 0.22/0.50    inference(global_subsumption,[],[f91,f1086])).
% 0.22/0.50  fof(f1086,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_25)),
% 0.22/0.50    inference(forward_demodulation,[],[f1077,f334])).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f332])).
% 0.22/0.50  fof(f332,plain,(
% 0.22/0.50    spl2_25 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.50  fof(f1077,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f74,f79,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  % (22740)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.50  fof(f948,plain,(
% 0.22/0.50    spl2_48 | ~spl2_45),
% 0.22/0.50    inference(avatar_split_clause,[],[f894,f891,f946])).
% 0.22/0.50  fof(f894,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(X0,k2_tops_1(sK0,sK1))))) ) | ~spl2_45),
% 0.22/0.50    inference(superposition,[],[f892,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.50  fof(f893,plain,(
% 0.22/0.50    spl2_45 | ~spl2_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f121,f97,f891])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k5_xboole_0(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),X0)))) ) | ~spl2_6),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f99,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f54,f56])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.50  fof(f866,plain,(
% 0.22/0.50    spl2_43 | ~spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f856,f72,f864])).
% 0.22/0.50  fof(f856,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_2),
% 0.22/0.50    inference(resolution,[],[f42,f74])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.50  fof(f349,plain,(
% 0.22/0.50    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) != k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f348,plain,(
% 0.22/0.50    spl2_26 | ~spl2_21 | ~spl2_23 | ~spl2_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f342,f325,f311,f287,f345])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    spl2_21 <=> ! [X0] : k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    spl2_23 <=> k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.50  fof(f325,plain,(
% 0.22/0.50    spl2_24 <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | (~spl2_21 | ~spl2_23 | ~spl2_24)),
% 0.22/0.50    inference(forward_demodulation,[],[f340,f327])).
% 0.22/0.50  fof(f327,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f325])).
% 0.22/0.50  fof(f340,plain,(
% 0.22/0.50    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_21 | ~spl2_23)),
% 0.22/0.50    inference(superposition,[],[f288,f313])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f311])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ) | ~spl2_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f287])).
% 0.22/0.50  fof(f335,plain,(
% 0.22/0.50    spl2_25 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f329,f86,f77,f72,f332])).
% 0.22/0.50  fof(f329,plain,(
% 0.22/0.50    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_4)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f74,f79,f88,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    v4_pre_topc(sK1,sK0) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f86])).
% 0.22/0.50  fof(f328,plain,(
% 0.22/0.50    spl2_24 | ~spl2_5 | ~spl2_10 | ~spl2_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f322,f306,f132,f90,f325])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    spl2_10 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    spl2_22 <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_5 | ~spl2_10 | ~spl2_22)),
% 0.22/0.50    inference(forward_demodulation,[],[f316,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f316,plain,(
% 0.22/0.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_10 | ~spl2_22)),
% 0.22/0.50    inference(superposition,[],[f133,f308])).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f306])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f132])).
% 0.22/0.50  fof(f309,plain,(
% 0.22/0.50    spl2_22 | ~spl2_5 | ~spl2_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f294,f287,f90,f306])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_21)),
% 0.22/0.50    inference(superposition,[],[f288,f92])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    spl2_21 | ~spl2_18 | ~spl2_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f282,f277,f211,f287])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    spl2_18 <=> ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.50  fof(f277,plain,(
% 0.22/0.50    spl2_20 <=> ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,X0)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) ) | (~spl2_18 | ~spl2_20)),
% 0.22/0.50    inference(superposition,[],[f212,f278])).
% 0.22/0.50  fof(f278,plain,(
% 0.22/0.50    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2)))) ) | ~spl2_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f277])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2))))) ) | ~spl2_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f211])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    spl2_20 | ~spl2_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f245,f132,f277])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2)))) ) | ~spl2_10),
% 0.22/0.50    inference(forward_demodulation,[],[f238,f133])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ( ! [X2] : (k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X2))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2)))) ) | ~spl2_10),
% 0.22/0.50    inference(superposition,[],[f62,f133])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f52,f56,f56,f48])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    spl2_18 | ~spl2_15 | ~spl2_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f209,f206,f188,f211])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    spl2_15 <=> ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    spl2_17 <=> ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X2))))) ) | (~spl2_15 | ~spl2_17)),
% 0.22/0.50    inference(forward_demodulation,[],[f207,f192])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    ( ! [X0] : (k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_15),
% 0.22/0.50    inference(superposition,[],[f189,f189])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))) ) | ~spl2_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f188])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))))) ) | ~spl2_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f206])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    spl2_17 | ~spl2_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f173,f132,f206])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))))) ) | ~spl2_10),
% 0.22/0.50    inference(superposition,[],[f61,f133])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    spl2_16 | ~spl2_5 | ~spl2_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f193,f188,f90,f200])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl2_16 <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_15)),
% 0.22/0.50    inference(superposition,[],[f189,f92])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    spl2_15 | ~spl2_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f185,f132,f188])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X2))) ) | ~spl2_10),
% 0.22/0.50    inference(forward_demodulation,[],[f176,f133])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X2))))) ) | ~spl2_10),
% 0.22/0.50    inference(superposition,[],[f61,f133])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl2_10 | ~spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f120,f77,f132])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_3),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f79,f63])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl2_6 | ~spl2_2 | ~spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f95,f77,f72,f97])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f74,f79,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ~spl2_4 | ~spl2_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f90,f86])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f16])).
% 0.22/0.50  fof(f16,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl2_4 | spl2_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f90,f86])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f77])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f72])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl2_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f67])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (22751)------------------------------
% 0.22/0.50  % (22751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22751)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (22751)Memory used [KB]: 12281
% 0.22/0.50  % (22751)Time elapsed: 0.085 s
% 0.22/0.50  % (22751)------------------------------
% 0.22/0.50  % (22751)------------------------------
% 0.22/0.50  % (22733)Success in time 0.139 s
%------------------------------------------------------------------------------
