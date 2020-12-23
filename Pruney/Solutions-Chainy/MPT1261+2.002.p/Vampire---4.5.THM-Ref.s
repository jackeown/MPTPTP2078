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
% DateTime   : Thu Dec  3 13:11:47 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 357 expanded)
%              Number of leaves         :   38 ( 129 expanded)
%              Depth                    :   15
%              Number of atoms          :  454 (1065 expanded)
%              Number of equality atoms :   99 ( 305 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f88,f205,f245,f248,f489,f1070,f1080,f1371,f1379,f1418,f1446,f1490,f1526,f1528,f1659,f1849,f2235])).

fof(f2235,plain,
    ( ~ spl2_6
    | ~ spl2_9
    | ~ spl2_5
    | spl2_50 ),
    inference(avatar_split_clause,[],[f2228,f1233,f195,f238,f199])).

fof(f199,plain,
    ( spl2_6
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f238,plain,
    ( spl2_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f195,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1233,plain,
    ( spl2_50
  <=> k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).

fof(f2228,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_50 ),
    inference(trivial_inequality_removal,[],[f2227])).

fof(f2227,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_50 ),
    inference(superposition,[],[f1234,f716])).

fof(f716,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X1,X0) = k5_xboole_0(X0,k2_tops_1(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ r1_tarski(k2_tops_1(X1,X0),X0) ) ),
    inference(superposition,[],[f229,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X1,X0)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f76,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f229,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k2_tops_1(X2,X3)))) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f228])).

fof(f228,plain,(
    ! [X2,X3] :
      ( k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k2_tops_1(X2,X3)))) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f78,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1234,plain,
    ( k1_tops_1(sK0,sK1) != k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_50 ),
    inference(avatar_component_clause,[],[f1233])).

fof(f1849,plain,
    ( ~ spl2_6
    | spl2_46 ),
    inference(avatar_contradiction_clause,[],[f1847])).

fof(f1847,plain,
    ( $false
    | ~ spl2_6
    | spl2_46 ),
    inference(resolution,[],[f1846,f201])).

fof(f201,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1846,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_46 ),
    inference(resolution,[],[f1135,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1135,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_46 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1134,plain,
    ( spl2_46
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f1659,plain,
    ( ~ spl2_6
    | ~ spl2_46
    | ~ spl2_50
    | spl2_47 ),
    inference(avatar_split_clause,[],[f1647,f1139,f1233,f1134,f199])).

fof(f1139,plain,
    ( spl2_47
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f1647,plain,
    ( k1_tops_1(sK0,sK1) != k5_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_47 ),
    inference(superposition,[],[f1140,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f77,f95])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f73])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1140,plain,
    ( k1_tops_1(sK0,sK1) != k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | spl2_47 ),
    inference(avatar_component_clause,[],[f1139])).

fof(f1528,plain,
    ( ~ spl2_9
    | ~ spl2_5
    | ~ spl2_53
    | spl2_54
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f1296,f1285,f1305,f1301,f195,f238])).

fof(f1301,plain,
    ( spl2_53
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f1305,plain,
    ( spl2_54
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f1285,plain,
    ( spl2_52
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f1296,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_52 ),
    inference(superposition,[],[f1287,f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f72,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1287,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f1526,plain,
    ( ~ spl2_46
    | spl2_52 ),
    inference(avatar_contradiction_clause,[],[f1524])).

fof(f1524,plain,
    ( $false
    | ~ spl2_46
    | spl2_52 ),
    inference(resolution,[],[f1513,f1136])).

fof(f1136,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1513,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_52 ),
    inference(trivial_inequality_removal,[],[f1511])).

fof(f1511,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_52 ),
    inference(superposition,[],[f1286,f941])).

fof(f941,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f937,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f937,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f925])).

fof(f925,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_xboole_0(X0,X1) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f668,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f668,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f666])).

fof(f666,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f145,f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f128,f72])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f66,f52])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f145,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k2_xboole_0(X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f75,f77])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f61,f73])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1286,plain,
    ( sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_52 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f1490,plain,
    ( ~ spl2_18
    | ~ spl2_5
    | ~ spl2_21
    | spl2_2 ),
    inference(avatar_split_clause,[],[f1484,f84,f482,f195,f468])).

fof(f468,plain,
    ( spl2_18
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f482,plain,
    ( spl2_21
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f84,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1484,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_2 ),
    inference(superposition,[],[f86,f181])).

fof(f181,plain,(
    ! [X6,X4,X5] :
      ( k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    inference(superposition,[],[f78,f77])).

fof(f86,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1446,plain,
    ( ~ spl2_46
    | spl2_21
    | ~ spl2_47 ),
    inference(avatar_split_clause,[],[f1222,f1139,f482,f1134])).

fof(f1222,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_47 ),
    inference(superposition,[],[f65,f1141])).

fof(f1141,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f1139])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1418,plain,(
    spl2_58 ),
    inference(avatar_contradiction_clause,[],[f1417])).

fof(f1417,plain,
    ( $false
    | spl2_58 ),
    inference(resolution,[],[f1378,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f43,plain,
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

fof(f44,plain,
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

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f1378,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_58 ),
    inference(avatar_component_clause,[],[f1376])).

fof(f1376,plain,
    ( spl2_58
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f1379,plain,
    ( ~ spl2_58
    | ~ spl2_9
    | ~ spl2_5
    | spl2_1
    | ~ spl2_54 ),
    inference(avatar_split_clause,[],[f1374,f1305,f80,f195,f238,f1376])).

fof(f80,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1374,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_54 ),
    inference(superposition,[],[f67,f1307])).

fof(f1307,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f1371,plain,
    ( ~ spl2_9
    | ~ spl2_5
    | spl2_53 ),
    inference(avatar_split_clause,[],[f1369,f1301,f195,f238])).

fof(f1369,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_53 ),
    inference(resolution,[],[f1303,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f1303,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_53 ),
    inference(avatar_component_clause,[],[f1301])).

fof(f1080,plain,
    ( ~ spl2_5
    | spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f191,f84,f199,f195])).

fof(f191,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f184,f85])).

fof(f85,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f184,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k7_subset_1(X8,X6,X7),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X8)) ) ),
    inference(superposition,[],[f74,f78])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1070,plain,
    ( ~ spl2_9
    | spl2_6
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f174,f80,f199,f238])).

fof(f174,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f489,plain,
    ( ~ spl2_10
    | spl2_18 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl2_10
    | spl2_18 ),
    inference(resolution,[],[f486,f244])).

fof(f244,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl2_10
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f486,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl2_18 ),
    inference(resolution,[],[f470,f70])).

fof(f470,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f468])).

fof(f248,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f240,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f240,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f238])).

fof(f245,plain,
    ( ~ spl2_9
    | spl2_10 ),
    inference(avatar_split_clause,[],[f235,f242,f238])).

fof(f235,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f230,f49])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f184,f54])).

fof(f205,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f197,f49])).

fof(f197,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f195])).

fof(f88,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f50,f84,f80])).

fof(f50,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f51,f84,f80])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:04:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (13150)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (13138)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (13151)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (13143)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (13145)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (13142)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (13147)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (13149)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (13144)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (13148)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (13152)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (13155)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (13154)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (13140)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (13141)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (13139)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (13153)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (13146)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.43/0.56  % (13142)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.56  % SZS output start Proof for theBenchmark
% 1.43/0.56  fof(f2236,plain,(
% 1.43/0.56    $false),
% 1.43/0.56    inference(avatar_sat_refutation,[],[f87,f88,f205,f245,f248,f489,f1070,f1080,f1371,f1379,f1418,f1446,f1490,f1526,f1528,f1659,f1849,f2235])).
% 1.43/0.56  fof(f2235,plain,(
% 1.43/0.56    ~spl2_6 | ~spl2_9 | ~spl2_5 | spl2_50),
% 1.43/0.56    inference(avatar_split_clause,[],[f2228,f1233,f195,f238,f199])).
% 1.43/0.56  fof(f199,plain,(
% 1.43/0.56    spl2_6 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.43/0.56  fof(f238,plain,(
% 1.43/0.56    spl2_9 <=> l1_pre_topc(sK0)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.43/0.56  fof(f195,plain,(
% 1.43/0.56    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.43/0.56  fof(f1233,plain,(
% 1.43/0.56    spl2_50 <=> k1_tops_1(sK0,sK1) = k5_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_50])])).
% 1.43/0.56  fof(f2228,plain,(
% 1.43/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_50),
% 1.43/0.56    inference(trivial_inequality_removal,[],[f2227])).
% 1.43/0.56  fof(f2227,plain,(
% 1.43/0.56    k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_50),
% 1.43/0.56    inference(superposition,[],[f1234,f716])).
% 1.43/0.56  fof(f716,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_tops_1(X1,X0) = k5_xboole_0(X0,k2_tops_1(X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~r1_tarski(k2_tops_1(X1,X0),X0)) )),
% 1.43/0.56    inference(superposition,[],[f229,f95])).
% 1.43/0.56  fof(f95,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.43/0.56    inference(superposition,[],[f76,f57])).
% 1.43/0.56  fof(f57,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f6])).
% 1.43/0.56  fof(f6,axiom,(
% 1.43/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.43/0.56  fof(f76,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f62,f59])).
% 1.43/0.56  fof(f59,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f14])).
% 1.43/0.56  fof(f14,axiom,(
% 1.43/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.43/0.56  fof(f62,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f29])).
% 1.43/0.56  fof(f29,plain,(
% 1.43/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f3])).
% 1.43/0.56  fof(f3,axiom,(
% 1.43/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.43/0.56  fof(f229,plain,(
% 1.43/0.56    ( ! [X2,X3] : (k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k2_tops_1(X2,X3)))) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f228])).
% 1.43/0.56  fof(f228,plain,(
% 1.43/0.56    ( ! [X2,X3] : (k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,k2_tops_1(X2,X3)))) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.43/0.56    inference(superposition,[],[f78,f54])).
% 1.43/0.56  fof(f54,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f26])).
% 1.43/0.56  fof(f26,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f20])).
% 1.43/0.56  fof(f20,axiom,(
% 1.43/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.43/0.56  fof(f78,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(definition_unfolding,[],[f71,f73])).
% 1.43/0.56  fof(f73,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.43/0.56    inference(definition_unfolding,[],[f60,f59])).
% 1.43/0.56  fof(f60,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f2])).
% 1.43/0.56  fof(f2,axiom,(
% 1.43/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.43/0.56  fof(f71,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f38])).
% 1.43/0.56  fof(f38,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f12])).
% 1.43/0.56  fof(f12,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.43/0.56  fof(f1234,plain,(
% 1.43/0.56    k1_tops_1(sK0,sK1) != k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_50),
% 1.43/0.56    inference(avatar_component_clause,[],[f1233])).
% 1.43/0.56  fof(f1849,plain,(
% 1.43/0.56    ~spl2_6 | spl2_46),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f1847])).
% 1.43/0.56  fof(f1847,plain,(
% 1.43/0.56    $false | (~spl2_6 | spl2_46)),
% 1.43/0.56    inference(resolution,[],[f1846,f201])).
% 1.43/0.56  fof(f201,plain,(
% 1.43/0.56    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_6),
% 1.43/0.56    inference(avatar_component_clause,[],[f199])).
% 1.43/0.56  fof(f1846,plain,(
% 1.43/0.56    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_46),
% 1.43/0.56    inference(resolution,[],[f1135,f70])).
% 1.43/0.56  fof(f70,plain,(
% 1.43/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f46])).
% 1.43/0.56  fof(f46,plain,(
% 1.43/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.43/0.56    inference(nnf_transformation,[],[f15])).
% 1.43/0.56  fof(f15,axiom,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.43/0.56  fof(f1135,plain,(
% 1.43/0.56    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_46),
% 1.43/0.56    inference(avatar_component_clause,[],[f1134])).
% 1.43/0.56  fof(f1134,plain,(
% 1.43/0.56    spl2_46 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 1.43/0.56  fof(f1659,plain,(
% 1.43/0.56    ~spl2_6 | ~spl2_46 | ~spl2_50 | spl2_47),
% 1.43/0.56    inference(avatar_split_clause,[],[f1647,f1139,f1233,f1134,f199])).
% 1.43/0.56  fof(f1139,plain,(
% 1.43/0.56    spl2_47 <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 1.43/0.56  fof(f1647,plain,(
% 1.43/0.56    k1_tops_1(sK0,sK1) != k5_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_47),
% 1.43/0.56    inference(superposition,[],[f1140,f143])).
% 1.43/0.56  fof(f143,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 1.43/0.56    inference(superposition,[],[f77,f95])).
% 1.43/0.56  fof(f77,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(definition_unfolding,[],[f64,f73])).
% 1.43/0.56  fof(f64,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f31])).
% 1.43/0.56  fof(f31,plain,(
% 1.43/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f8])).
% 1.43/0.56  fof(f8,axiom,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.43/0.56  fof(f1140,plain,(
% 1.43/0.56    k1_tops_1(sK0,sK1) != k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | spl2_47),
% 1.43/0.56    inference(avatar_component_clause,[],[f1139])).
% 1.43/0.56  fof(f1528,plain,(
% 1.43/0.56    ~spl2_9 | ~spl2_5 | ~spl2_53 | spl2_54 | ~spl2_52),
% 1.43/0.56    inference(avatar_split_clause,[],[f1296,f1285,f1305,f1301,f195,f238])).
% 1.43/0.56  fof(f1301,plain,(
% 1.43/0.56    spl2_53 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 1.43/0.56  fof(f1305,plain,(
% 1.43/0.56    spl2_54 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 1.43/0.56  fof(f1285,plain,(
% 1.43/0.56    spl2_52 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 1.43/0.56  fof(f1296,plain,(
% 1.43/0.56    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_52),
% 1.43/0.56    inference(superposition,[],[f1287,f222])).
% 1.43/0.56  fof(f222,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f221])).
% 1.43/0.56  fof(f221,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.56    inference(superposition,[],[f72,f53])).
% 1.43/0.56  fof(f53,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f25])).
% 1.43/0.56  fof(f25,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f18])).
% 1.43/0.56  fof(f18,axiom,(
% 1.43/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.43/0.56  fof(f72,plain,(
% 1.43/0.56    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f40])).
% 1.43/0.56  fof(f40,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(flattening,[],[f39])).
% 1.43/0.56  fof(f39,plain,(
% 1.43/0.56    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.43/0.56    inference(ennf_transformation,[],[f11])).
% 1.43/0.56  fof(f11,axiom,(
% 1.43/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.43/0.56  fof(f1287,plain,(
% 1.43/0.56    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_52),
% 1.43/0.56    inference(avatar_component_clause,[],[f1285])).
% 1.43/0.56  fof(f1526,plain,(
% 1.43/0.56    ~spl2_46 | spl2_52),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f1524])).
% 1.43/0.56  fof(f1524,plain,(
% 1.43/0.56    $false | (~spl2_46 | spl2_52)),
% 1.43/0.56    inference(resolution,[],[f1513,f1136])).
% 1.43/0.56  fof(f1136,plain,(
% 1.43/0.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_46),
% 1.43/0.56    inference(avatar_component_clause,[],[f1134])).
% 1.43/0.56  fof(f1513,plain,(
% 1.43/0.56    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_52),
% 1.43/0.56    inference(trivial_inequality_removal,[],[f1511])).
% 1.43/0.56  fof(f1511,plain,(
% 1.43/0.56    sK1 != sK1 | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_52),
% 1.43/0.56    inference(superposition,[],[f1286,f941])).
% 1.43/0.56  fof(f941,plain,(
% 1.43/0.56    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 1.43/0.56    inference(superposition,[],[f937,f58])).
% 1.43/0.56  fof(f58,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f1])).
% 1.43/0.56  fof(f1,axiom,(
% 1.43/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.43/0.56  fof(f937,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f925])).
% 1.43/0.56  fof(f925,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X1) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.43/0.56    inference(resolution,[],[f668,f63])).
% 1.43/0.56  fof(f63,plain,(
% 1.43/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f30])).
% 1.43/0.56  fof(f30,plain,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f9])).
% 1.43/0.56  fof(f9,axiom,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.43/0.56  fof(f668,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k2_xboole_0(X0,X1) = X1) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f666])).
% 1.43/0.56  fof(f666,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1))) )),
% 1.43/0.56    inference(superposition,[],[f145,f208])).
% 1.43/0.56  fof(f208,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f207])).
% 1.43/0.56  fof(f207,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_xboole_0(X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(superposition,[],[f128,f72])).
% 1.43/0.56  fof(f128,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(forward_demodulation,[],[f66,f52])).
% 1.43/0.56  fof(f52,plain,(
% 1.43/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.43/0.56    inference(cnf_transformation,[],[f7])).
% 1.43/0.56  fof(f7,axiom,(
% 1.43/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.43/0.56  fof(f66,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f33])).
% 1.43/0.56  fof(f33,plain,(
% 1.43/0.56    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f13])).
% 1.43/0.56  fof(f13,axiom,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.43/0.56  fof(f145,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(superposition,[],[f75,f77])).
% 1.43/0.56  fof(f75,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 1.43/0.56    inference(definition_unfolding,[],[f61,f73])).
% 1.43/0.56  fof(f61,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f5])).
% 1.43/0.56  fof(f5,axiom,(
% 1.43/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.43/0.56  fof(f1286,plain,(
% 1.43/0.56    sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_52),
% 1.43/0.56    inference(avatar_component_clause,[],[f1285])).
% 1.43/0.56  fof(f1490,plain,(
% 1.43/0.56    ~spl2_18 | ~spl2_5 | ~spl2_21 | spl2_2),
% 1.43/0.56    inference(avatar_split_clause,[],[f1484,f84,f482,f195,f468])).
% 1.43/0.56  fof(f468,plain,(
% 1.43/0.56    spl2_18 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.43/0.56  fof(f482,plain,(
% 1.43/0.56    spl2_21 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.43/0.56  fof(f84,plain,(
% 1.43/0.56    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.43/0.56  fof(f1484,plain,(
% 1.43/0.56    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_2),
% 1.43/0.56    inference(superposition,[],[f86,f181])).
% 1.43/0.56  fof(f181,plain,(
% 1.43/0.56    ( ! [X6,X4,X5] : (k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(X6)) | ~m1_subset_1(X5,k1_zfmisc_1(X4))) )),
% 1.43/0.56    inference(superposition,[],[f78,f77])).
% 1.43/0.56  fof(f86,plain,(
% 1.43/0.56    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 1.43/0.56    inference(avatar_component_clause,[],[f84])).
% 1.43/0.56  fof(f1446,plain,(
% 1.43/0.56    ~spl2_46 | spl2_21 | ~spl2_47),
% 1.43/0.56    inference(avatar_split_clause,[],[f1222,f1139,f482,f1134])).
% 1.43/0.56  fof(f1222,plain,(
% 1.43/0.56    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_47),
% 1.43/0.56    inference(superposition,[],[f65,f1141])).
% 1.43/0.56  fof(f1141,plain,(
% 1.43/0.56    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_47),
% 1.43/0.56    inference(avatar_component_clause,[],[f1139])).
% 1.43/0.56  fof(f65,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f32])).
% 1.43/0.56  fof(f32,plain,(
% 1.43/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f10])).
% 1.43/0.56  fof(f10,axiom,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.43/0.56  fof(f1418,plain,(
% 1.43/0.56    spl2_58),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f1417])).
% 1.43/0.56  fof(f1417,plain,(
% 1.43/0.56    $false | spl2_58),
% 1.43/0.56    inference(resolution,[],[f1378,f47])).
% 1.43/0.56  fof(f47,plain,(
% 1.43/0.56    v2_pre_topc(sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f45])).
% 1.43/0.56  fof(f45,plain,(
% 1.43/0.56    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 1.43/0.56  fof(f43,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f44,plain,(
% 1.43/0.56    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f42,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.43/0.56    inference(flattening,[],[f41])).
% 1.43/0.56  fof(f41,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.43/0.56    inference(nnf_transformation,[],[f24])).
% 1.43/0.56  fof(f24,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.43/0.56    inference(flattening,[],[f23])).
% 1.43/0.56  fof(f23,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f22])).
% 1.43/0.56  fof(f22,negated_conjecture,(
% 1.43/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.43/0.56    inference(negated_conjecture,[],[f21])).
% 1.43/0.56  fof(f21,conjecture,(
% 1.43/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.43/0.56  fof(f1378,plain,(
% 1.43/0.56    ~v2_pre_topc(sK0) | spl2_58),
% 1.43/0.56    inference(avatar_component_clause,[],[f1376])).
% 1.43/0.56  fof(f1376,plain,(
% 1.43/0.56    spl2_58 <=> v2_pre_topc(sK0)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 1.43/0.56  fof(f1379,plain,(
% 1.43/0.56    ~spl2_58 | ~spl2_9 | ~spl2_5 | spl2_1 | ~spl2_54),
% 1.43/0.56    inference(avatar_split_clause,[],[f1374,f1305,f80,f195,f238,f1376])).
% 1.43/0.56  fof(f80,plain,(
% 1.43/0.56    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.43/0.56  fof(f1374,plain,(
% 1.43/0.56    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_54),
% 1.43/0.56    inference(superposition,[],[f67,f1307])).
% 1.43/0.56  fof(f1307,plain,(
% 1.43/0.56    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_54),
% 1.43/0.56    inference(avatar_component_clause,[],[f1305])).
% 1.43/0.56  fof(f67,plain,(
% 1.43/0.56    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f35])).
% 1.43/0.56  fof(f35,plain,(
% 1.43/0.56    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.43/0.56    inference(flattening,[],[f34])).
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f17])).
% 1.43/0.56  fof(f17,axiom,(
% 1.43/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.43/0.56  fof(f1371,plain,(
% 1.43/0.56    ~spl2_9 | ~spl2_5 | spl2_53),
% 1.43/0.56    inference(avatar_split_clause,[],[f1369,f1301,f195,f238])).
% 1.43/0.56  fof(f1369,plain,(
% 1.43/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_53),
% 1.43/0.56    inference(resolution,[],[f1303,f68])).
% 1.43/0.56  fof(f68,plain,(
% 1.43/0.56    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f37])).
% 1.43/0.56  fof(f37,plain,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(flattening,[],[f36])).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f16])).
% 1.43/0.56  fof(f16,axiom,(
% 1.43/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.43/0.56  fof(f1303,plain,(
% 1.43/0.56    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_53),
% 1.43/0.56    inference(avatar_component_clause,[],[f1301])).
% 1.43/0.56  fof(f1080,plain,(
% 1.43/0.56    ~spl2_5 | spl2_6 | ~spl2_2),
% 1.43/0.56    inference(avatar_split_clause,[],[f191,f84,f199,f195])).
% 1.43/0.56  fof(f191,plain,(
% 1.43/0.56    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.43/0.56    inference(superposition,[],[f184,f85])).
% 1.43/0.56  fof(f85,plain,(
% 1.43/0.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 1.43/0.56    inference(avatar_component_clause,[],[f84])).
% 1.43/0.56  fof(f184,plain,(
% 1.43/0.56    ( ! [X6,X8,X7] : (r1_tarski(k7_subset_1(X8,X6,X7),X6) | ~m1_subset_1(X6,k1_zfmisc_1(X8))) )),
% 1.43/0.56    inference(superposition,[],[f74,f78])).
% 1.43/0.56  fof(f74,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f56,f73])).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f4])).
% 1.43/0.56  fof(f4,axiom,(
% 1.43/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.43/0.56  fof(f1070,plain,(
% 1.43/0.56    ~spl2_9 | spl2_6 | ~spl2_1),
% 1.43/0.56    inference(avatar_split_clause,[],[f174,f80,f199,f238])).
% 1.43/0.56  fof(f174,plain,(
% 1.43/0.56    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.43/0.56    inference(resolution,[],[f55,f49])).
% 1.43/0.56  fof(f49,plain,(
% 1.43/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.56    inference(cnf_transformation,[],[f45])).
% 1.43/0.56  fof(f55,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f28])).
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(flattening,[],[f27])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f19])).
% 1.43/0.56  fof(f19,axiom,(
% 1.43/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 1.43/0.56  fof(f489,plain,(
% 1.43/0.56    ~spl2_10 | spl2_18),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f487])).
% 1.43/0.56  fof(f487,plain,(
% 1.43/0.56    $false | (~spl2_10 | spl2_18)),
% 1.43/0.56    inference(resolution,[],[f486,f244])).
% 1.43/0.56  fof(f244,plain,(
% 1.43/0.56    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_10),
% 1.43/0.56    inference(avatar_component_clause,[],[f242])).
% 1.43/0.56  fof(f242,plain,(
% 1.43/0.56    spl2_10 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.43/0.56  fof(f486,plain,(
% 1.43/0.56    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl2_18),
% 1.43/0.56    inference(resolution,[],[f470,f70])).
% 1.43/0.56  fof(f470,plain,(
% 1.43/0.56    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_18),
% 1.43/0.56    inference(avatar_component_clause,[],[f468])).
% 1.43/0.56  fof(f248,plain,(
% 1.43/0.56    spl2_9),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f247])).
% 1.43/0.56  fof(f247,plain,(
% 1.43/0.56    $false | spl2_9),
% 1.43/0.56    inference(resolution,[],[f240,f48])).
% 1.43/0.56  fof(f48,plain,(
% 1.43/0.56    l1_pre_topc(sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f45])).
% 1.43/0.56  fof(f240,plain,(
% 1.43/0.56    ~l1_pre_topc(sK0) | spl2_9),
% 1.43/0.56    inference(avatar_component_clause,[],[f238])).
% 1.43/0.56  fof(f245,plain,(
% 1.43/0.56    ~spl2_9 | spl2_10),
% 1.43/0.56    inference(avatar_split_clause,[],[f235,f242,f238])).
% 1.43/0.56  fof(f235,plain,(
% 1.43/0.56    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 1.43/0.56    inference(resolution,[],[f230,f49])).
% 1.43/0.56  fof(f230,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f227])).
% 1.43/0.56  fof(f227,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.43/0.56    inference(superposition,[],[f184,f54])).
% 1.43/0.56  fof(f205,plain,(
% 1.43/0.56    spl2_5),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f203])).
% 1.43/0.56  fof(f203,plain,(
% 1.43/0.56    $false | spl2_5),
% 1.43/0.56    inference(resolution,[],[f197,f49])).
% 1.43/0.56  fof(f197,plain,(
% 1.43/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_5),
% 1.43/0.56    inference(avatar_component_clause,[],[f195])).
% 1.43/0.56  fof(f88,plain,(
% 1.43/0.56    spl2_1 | spl2_2),
% 1.43/0.56    inference(avatar_split_clause,[],[f50,f84,f80])).
% 1.43/0.56  fof(f50,plain,(
% 1.43/0.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f45])).
% 1.43/0.56  fof(f87,plain,(
% 1.43/0.56    ~spl2_1 | ~spl2_2),
% 1.43/0.56    inference(avatar_split_clause,[],[f51,f84,f80])).
% 1.43/0.56  fof(f51,plain,(
% 1.43/0.56    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f45])).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (13142)------------------------------
% 1.43/0.56  % (13142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (13142)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (13142)Memory used [KB]: 7164
% 1.43/0.56  % (13142)Time elapsed: 0.121 s
% 1.43/0.56  % (13142)------------------------------
% 1.43/0.56  % (13142)------------------------------
% 1.43/0.56  % (13137)Success in time 0.204 s
%------------------------------------------------------------------------------
