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
% DateTime   : Thu Dec  3 13:12:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 307 expanded)
%              Number of leaves         :   28 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          :  342 ( 926 expanded)
%              Number of equality atoms :   94 ( 305 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1918,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f69,f120,f174,f176,f609,f1152,f1612,f1619,f1620,f1637,f1667,f1895,f1917])).

fof(f1917,plain,
    ( ~ spl2_8
    | ~ spl2_3
    | spl2_70 ),
    inference(avatar_split_clause,[],[f1916,f1891,f110,f161])).

fof(f161,plain,
    ( spl2_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f110,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1891,plain,
    ( spl2_70
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f1916,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_70 ),
    inference(resolution,[],[f1893,f53])).

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

fof(f1893,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_70 ),
    inference(avatar_component_clause,[],[f1891])).

fof(f1895,plain,
    ( ~ spl2_8
    | ~ spl2_3
    | ~ spl2_70
    | spl2_10
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f1886,f1606,f169,f1891,f110,f161])).

fof(f169,plain,
    ( spl2_10
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f1606,plain,
    ( spl2_61
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f1886,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_61 ),
    inference(superposition,[],[f179,f1863])).

fof(f1863,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f1843,f41])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f1843,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_61 ),
    inference(superposition,[],[f51,f1806])).

fof(f1806,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f1784,f1346])).

fof(f1346,plain,(
    ! [X11] : k1_xboole_0 = k5_xboole_0(X11,X11) ),
    inference(forward_demodulation,[],[f1315,f42])).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1315,plain,(
    ! [X11] : k1_xboole_0 = k5_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0)) ),
    inference(superposition,[],[f95,f1250])).

fof(f1250,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f87,f1239])).

fof(f1239,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f1037,f144])).

fof(f144,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) ),
    inference(superposition,[],[f93,f42])).

fof(f93,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4) ),
    inference(superposition,[],[f47,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f48,f49,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1037,plain,(
    ! [X6] :
      ( ~ r1_tarski(X6,k1_xboole_0)
      | k1_xboole_0 = X6 ) ),
    inference(resolution,[],[f311,f73])).

fof(f73,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f71,f47])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0)
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f55,f41])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f311,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,X6)
      | X6 = X7
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f88,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f49])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f88,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f58,f59])).

fof(f87,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f58,f42])).

fof(f95,plain,(
    ! [X8,X9] : k4_xboole_0(X9,k4_xboole_0(X9,X8)) = k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X9,X8)))) ),
    inference(superposition,[],[f57,f58])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1784,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_61 ),
    inference(superposition,[],[f91,f1608])).

fof(f1608,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f1606])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f57,f58])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f179,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f56,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1667,plain,
    ( ~ spl2_43
    | spl2_61
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f1665,f114,f1606,f1108])).

fof(f1108,plain,
    ( spl2_43
  <=> r1_tarski(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f114,plain,
    ( spl2_4
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1665,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ r1_tarski(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1)
    | ~ spl2_4 ),
    inference(superposition,[],[f317,f123])).

fof(f123,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_4 ),
    inference(superposition,[],[f57,f116])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f317,plain,(
    ! [X6,X7] :
      ( k4_xboole_0(X6,X7) = k5_xboole_0(X6,X7)
      | ~ r1_tarski(X7,X6) ) ),
    inference(superposition,[],[f57,f88])).

fof(f1637,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f1635,f65,f114,f110])).

fof(f65,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1635,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f54,f66])).

fof(f66,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1620,plain,
    ( ~ spl2_8
    | ~ spl2_3
    | spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f1617,f169,f65,f110,f161])).

fof(f1617,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10 ),
    inference(superposition,[],[f44,f170])).

fof(f170,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f1619,plain,
    ( ~ spl2_8
    | ~ spl2_3
    | spl2_4
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f1618,f169,f114,f110,f161])).

fof(f1618,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_10 ),
    inference(duplicate_literal_removal,[],[f1616])).

fof(f1616,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(superposition,[],[f181,f170])).

fof(f181,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f44,f54])).

fof(f1612,plain,
    ( ~ spl2_8
    | spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f140,f61,f169,f161])).

fof(f61,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f140,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f1152,plain,(
    spl2_43 ),
    inference(avatar_contradiction_clause,[],[f1150])).

fof(f1150,plain,
    ( $false
    | spl2_43 ),
    inference(resolution,[],[f1110,f47])).

fof(f1110,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1)
    | spl2_43 ),
    inference(avatar_component_clause,[],[f1108])).

fof(f609,plain,
    ( ~ spl2_8
    | spl2_1
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f607,f169,f165,f61,f161])).

fof(f165,plain,
    ( spl2_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f607,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f176,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f167,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f167,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f174,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f163,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f161])).

fof(f120,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f112,f38])).

fof(f112,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f69,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f39,f65,f61])).

fof(f39,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f40,f65,f61])).

fof(f40,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (13668)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (13673)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (13665)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (13678)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (13669)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (13674)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (13670)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (13680)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (13682)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (13672)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (13677)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (13671)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (13676)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (13667)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (13679)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (13666)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (13675)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.51  % (13681)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (13669)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f1918,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f68,f69,f120,f174,f176,f609,f1152,f1612,f1619,f1620,f1637,f1667,f1895,f1917])).
% 0.20/0.52  fof(f1917,plain,(
% 0.20/0.52    ~spl2_8 | ~spl2_3 | spl2_70),
% 0.20/0.52    inference(avatar_split_clause,[],[f1916,f1891,f110,f161])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    spl2_8 <=> l1_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.52  fof(f1891,plain,(
% 0.20/0.52    spl2_70 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 0.20/0.52  fof(f1916,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_70),
% 0.20/0.52    inference(resolution,[],[f1893,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.20/0.52  fof(f1893,plain,(
% 0.20/0.52    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_70),
% 0.20/0.52    inference(avatar_component_clause,[],[f1891])).
% 0.20/0.52  fof(f1895,plain,(
% 0.20/0.52    ~spl2_8 | ~spl2_3 | ~spl2_70 | spl2_10 | ~spl2_61),
% 0.20/0.52    inference(avatar_split_clause,[],[f1886,f1606,f169,f1891,f110,f161])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    spl2_10 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.52  fof(f1606,plain,(
% 0.20/0.52    spl2_61 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 0.20/0.53  fof(f1886,plain,(
% 0.20/0.53    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_61),
% 0.20/0.53    inference(superposition,[],[f179,f1863])).
% 0.20/0.53  fof(f1863,plain,(
% 0.20/0.53    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_61),
% 0.20/0.53    inference(forward_demodulation,[],[f1843,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.53  fof(f1843,plain,(
% 0.20/0.53    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0) | ~spl2_61),
% 0.20/0.53    inference(superposition,[],[f51,f1806])).
% 0.20/0.53  fof(f1806,plain,(
% 0.20/0.53    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_61),
% 0.20/0.53    inference(forward_demodulation,[],[f1784,f1346])).
% 0.20/0.53  fof(f1346,plain,(
% 0.20/0.53    ( ! [X11] : (k1_xboole_0 = k5_xboole_0(X11,X11)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f1315,f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.53  fof(f1315,plain,(
% 0.20/0.53    ( ! [X11] : (k1_xboole_0 = k5_xboole_0(X11,k4_xboole_0(X11,k1_xboole_0))) )),
% 0.20/0.53    inference(superposition,[],[f95,f1250])).
% 0.20/0.53  fof(f1250,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.20/0.53    inference(backward_demodulation,[],[f87,f1239])).
% 0.20/0.53  fof(f1239,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.53    inference(resolution,[],[f1037,f144])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0)) )),
% 0.20/0.53    inference(superposition,[],[f93,f42])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) )),
% 0.20/0.53    inference(superposition,[],[f47,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f48,f49,f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.53  fof(f1037,plain,(
% 0.20/0.53    ( ! [X6] : (~r1_tarski(X6,k1_xboole_0) | k1_xboole_0 = X6) )),
% 0.20/0.53    inference(resolution,[],[f311,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(resolution,[],[f71,f47])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X1,X0),k1_xboole_0) | r1_tarski(X1,X0)) )),
% 0.20/0.53    inference(superposition,[],[f55,f41])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.20/0.53  fof(f311,plain,(
% 0.20/0.53    ( ! [X6,X7] : (~r1_tarski(X7,X6) | X6 = X7 | ~r1_tarski(X6,X7)) )),
% 0.20/0.53    inference(superposition,[],[f88,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f52,f49])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 0.20/0.53    inference(superposition,[],[f58,f59])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 0.20/0.53    inference(superposition,[],[f58,f42])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ( ! [X8,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,X8)) = k5_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X9,X8))))) )),
% 0.20/0.53    inference(superposition,[],[f57,f58])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f50,f49])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.53  fof(f1784,plain,(
% 0.20/0.53    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_61),
% 0.20/0.53    inference(superposition,[],[f91,f1608])).
% 0.20/0.53  fof(f1608,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_61),
% 0.20/0.53    inference(avatar_component_clause,[],[f1606])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.20/0.53    inference(superposition,[],[f57,f58])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f178])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(superposition,[],[f56,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.53  fof(f1667,plain,(
% 0.20/0.53    ~spl2_43 | spl2_61 | ~spl2_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f1665,f114,f1606,f1108])).
% 0.20/0.53  fof(f1108,plain,(
% 0.20/0.53    spl2_43 <=> r1_tarski(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    spl2_4 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.53  fof(f1665,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~r1_tarski(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1) | ~spl2_4),
% 0.20/0.53    inference(superposition,[],[f317,f123])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_4),
% 0.20/0.53    inference(superposition,[],[f57,f116])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f114])).
% 0.20/0.53  fof(f317,plain,(
% 0.20/0.53    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k5_xboole_0(X6,X7) | ~r1_tarski(X7,X6)) )),
% 0.20/0.53    inference(superposition,[],[f57,f88])).
% 0.20/0.53  fof(f1637,plain,(
% 0.20/0.53    ~spl2_3 | spl2_4 | ~spl2_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f1635,f65,f114,f110])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.53  fof(f1635,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.20/0.53    inference(superposition,[],[f54,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f65])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.20/0.53  fof(f1620,plain,(
% 0.20/0.53    ~spl2_8 | ~spl2_3 | spl2_2 | ~spl2_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f1617,f169,f65,f110,f161])).
% 0.20/0.53  fof(f1617,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_10),
% 0.20/0.53    inference(superposition,[],[f44,f170])).
% 0.20/0.53  fof(f170,plain,(
% 0.20/0.53    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f169])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.20/0.53  fof(f1619,plain,(
% 0.20/0.53    ~spl2_8 | ~spl2_3 | spl2_4 | ~spl2_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f1618,f169,f114,f110,f161])).
% 0.20/0.53  fof(f1618,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_10),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f1616])).
% 0.20/0.53  fof(f1616,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_10),
% 0.20/0.53    inference(superposition,[],[f181,f170])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.20/0.53    inference(superposition,[],[f44,f54])).
% 0.20/0.53  fof(f1612,plain,(
% 0.20/0.53    ~spl2_8 | spl2_10 | ~spl2_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f140,f61,f169,f161])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.53    inference(resolution,[],[f45,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f16])).
% 0.20/0.53  fof(f16,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.53  fof(f1152,plain,(
% 0.20/0.53    spl2_43),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1150])).
% 0.20/0.53  fof(f1150,plain,(
% 0.20/0.53    $false | spl2_43),
% 0.20/0.53    inference(resolution,[],[f1110,f47])).
% 0.20/0.53  fof(f1110,plain,(
% 0.20/0.53    ~r1_tarski(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1) | spl2_43),
% 0.20/0.53    inference(avatar_component_clause,[],[f1108])).
% 0.20/0.53  fof(f609,plain,(
% 0.20/0.53    ~spl2_8 | spl2_1 | ~spl2_9 | ~spl2_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f607,f169,f165,f61,f161])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    spl2_9 <=> v2_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.53  fof(f607,plain,(
% 0.20/0.53    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.53    inference(resolution,[],[f38,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    spl2_9),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    $false | spl2_9),
% 0.20/0.53    inference(resolution,[],[f167,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    ~v2_pre_topc(sK0) | spl2_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f165])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    spl2_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.53  fof(f173,plain,(
% 0.20/0.53    $false | spl2_8),
% 0.20/0.53    inference(resolution,[],[f163,f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | spl2_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f161])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    spl2_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    $false | spl2_3),
% 0.20/0.53    inference(resolution,[],[f112,f38])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f110])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    spl2_1 | spl2_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f39,f65,f61])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ~spl2_1 | ~spl2_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f40,f65,f61])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (13669)------------------------------
% 0.20/0.53  % (13669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13669)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (13669)Memory used [KB]: 6908
% 0.20/0.53  % (13669)Time elapsed: 0.113 s
% 0.20/0.53  % (13669)------------------------------
% 0.20/0.53  % (13669)------------------------------
% 0.20/0.53  % (13664)Success in time 0.173 s
%------------------------------------------------------------------------------
