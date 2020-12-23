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
% DateTime   : Thu Dec  3 13:11:35 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 294 expanded)
%              Number of leaves         :   37 ( 112 expanded)
%              Depth                    :   13
%              Number of atoms          :  451 ( 923 expanded)
%              Number of equality atoms :   81 ( 213 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f121,f124,f207,f299,f457,f496,f499,f504,f597,f601,f611,f1209,f1289,f1345,f1380,f1381])).

fof(f1381,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1380,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_30
    | ~ spl2_49 ),
    inference(avatar_split_clause,[],[f1372,f1342,f608,f109,f104])).

fof(f104,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f109,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f608,plain,
    ( spl2_30
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f1342,plain,
    ( spl2_49
  <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f1372,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_49 ),
    inference(superposition,[],[f1344,f349])).

fof(f349,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f91,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f66,f89])).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1344,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f1345,plain,
    ( ~ spl2_18
    | spl2_49
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f1303,f493,f1342,f485])).

fof(f485,plain,
    ( spl2_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f493,plain,
    ( spl2_20
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1303,plain,
    ( sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_20 ),
    inference(superposition,[],[f961,f495])).

fof(f495,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f493])).

fof(f961,plain,(
    ! [X10,X11] :
      ( k5_xboole_0(X11,k3_xboole_0(X11,k3_subset_1(X10,X11))) = X11
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) ) ),
    inference(duplicate_literal_removal,[],[f960])).

fof(f960,plain,(
    ! [X10,X11] :
      ( k5_xboole_0(X11,k3_xboole_0(X11,k3_subset_1(X10,X11))) = X11
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10)) ) ),
    inference(superposition,[],[f91,f936])).

fof(f936,plain,(
    ! [X4,X5] :
      ( k7_subset_1(X4,X5,k3_subset_1(X4,X5)) = X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    inference(global_subsumption,[],[f83,f932])).

fof(f932,plain,(
    ! [X4,X5] :
      ( k7_subset_1(X4,X5,k3_subset_1(X4,X5)) = X5
      | ~ m1_subset_1(k3_subset_1(X4,X5),k1_zfmisc_1(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    inference(duplicate_literal_removal,[],[f905])).

fof(f905,plain,(
    ! [X4,X5] :
      ( k7_subset_1(X4,X5,k3_subset_1(X4,X5)) = X5
      | ~ m1_subset_1(k3_subset_1(X4,X5),k1_zfmisc_1(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    inference(superposition,[],[f365,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f365,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(condensation,[],[f364])).

fof(f364,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f81,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1289,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f1224,f608,f118,f109,f104])).

fof(f118,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1224,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_30 ),
    inference(superposition,[],[f68,f610])).

fof(f610,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f608])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1209,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_29 ),
    inference(avatar_contradiction_clause,[],[f1200])).

fof(f1200,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_29 ),
    inference(unit_resulting_resolution,[],[f106,f606,f111,f1056])).

fof(f1056,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X11)))
      | r1_tarski(k1_tops_1(X11,X10),X10)
      | ~ l1_pre_topc(X11) ) ),
    inference(superposition,[],[f1038,f349])).

fof(f1038,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(resolution,[],[f895,f87])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f895,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X0,k3_xboole_0(X0,X1)),X0)
      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ) ),
    inference(resolution,[],[f777,f76])).

fof(f76,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f777,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(k3_xboole_0(X6,k3_xboole_0(X6,X7)),k1_zfmisc_1(X6))
      | r1_tarski(k5_xboole_0(X6,k3_xboole_0(X6,X7)),X6) ) ),
    inference(superposition,[],[f552,f93])).

fof(f93,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f78,f89,f89])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f552,plain,(
    ! [X8,X7] :
      ( r1_tarski(k5_xboole_0(X7,k3_xboole_0(X7,X8)),X7)
      | ~ m1_subset_1(k3_xboole_0(X7,X8),k1_zfmisc_1(X7)) ) ),
    inference(duplicate_literal_removal,[],[f540])).

fof(f540,plain,(
    ! [X8,X7] :
      ( r1_tarski(k5_xboole_0(X7,k3_xboole_0(X7,X8)),X7)
      | ~ m1_subset_1(k3_xboole_0(X7,X8),k1_zfmisc_1(X7))
      | ~ m1_subset_1(k3_xboole_0(X7,X8),k1_zfmisc_1(X7)) ) ),
    inference(superposition,[],[f160,f238])).

fof(f238,plain,(
    ! [X2,X3] :
      ( k3_subset_1(X2,k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,X3))
      | ~ m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f93,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f89])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f160,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X1,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f83,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f111,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f606,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl2_29 ),
    inference(avatar_component_clause,[],[f604])).

fof(f604,plain,
    ( spl2_29
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f106,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f611,plain,
    ( ~ spl2_29
    | spl2_30
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f602,f590,f608,f604])).

fof(f590,plain,
    ( spl2_27
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f602,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_27 ),
    inference(resolution,[],[f592,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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

fof(f592,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f590])).

fof(f601,plain,(
    spl2_28 ),
    inference(avatar_contradiction_clause,[],[f598])).

fof(f598,plain,
    ( $false
    | spl2_28 ),
    inference(unit_resulting_resolution,[],[f96,f596])).

fof(f596,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl2_28 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl2_28
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f597,plain,
    ( ~ spl2_4
    | spl2_27
    | ~ spl2_28
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f462,f455,f109,f594,f590,f114])).

fof(f114,plain,
    ( spl2_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f455,plain,
    ( spl2_17
  <=> ! [X11] :
        ( ~ r1_tarski(X11,sK1)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X11,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X11,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f462,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(resolution,[],[f456,f111])).

fof(f456,plain,
    ( ! [X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X11,sK1)
        | r1_tarski(X11,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X11,sK0) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f455])).

fof(f504,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_19 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_19 ),
    inference(unit_resulting_resolution,[],[f106,f111,f491,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f491,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl2_19
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f499,plain,
    ( ~ spl2_13
    | spl2_18 ),
    inference(avatar_contradiction_clause,[],[f497])).

fof(f497,plain,
    ( $false
    | ~ spl2_13
    | spl2_18 ),
    inference(unit_resulting_resolution,[],[f206,f487,f76])).

fof(f487,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f485])).

fof(f206,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl2_13
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f496,plain,
    ( ~ spl2_18
    | ~ spl2_19
    | spl2_20
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f427,f118,f493,f489,f485])).

fof(f427,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_5 ),
    inference(superposition,[],[f320,f120])).

fof(f120,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f320,plain,(
    ! [X6,X8,X7] :
      ( k3_subset_1(X6,X7) = k7_subset_1(X8,X6,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X8))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f91,f92])).

fof(f457,plain,
    ( ~ spl2_2
    | spl2_17
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f452,f109,f455,f104])).

fof(f452,plain,
    ( ! [X11] :
        ( ~ r1_tarski(X11,sK1)
        | ~ v3_pre_topc(X11,sK0)
        | r1_tarski(X11,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f74,f111])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f299,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_16
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f293,f109,f296,f104,f99])).

fof(f99,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f296,plain,
    ( spl2_16
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f293,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f73,f111])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f207,plain,
    ( ~ spl2_2
    | spl2_13
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f202,f109,f204,f104])).

fof(f202,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f71,f111])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f124,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f123,f118,f114])).

fof(f123,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f65,f120])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f121,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f64,f118,f114])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f112,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f63,f109])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f107,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f62,f104])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f102,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f61,f99])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:24:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (9921)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (9930)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (9938)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (9924)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (9920)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (9935)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (9940)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (9925)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (9929)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (9926)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (9939)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (9927)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (9933)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (9932)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (9918)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (9945)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (9946)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (9916)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (9942)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (9917)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (9931)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (9937)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (9943)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (9934)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (9919)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (9941)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (9922)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (9944)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (9933)Refutation not found, incomplete strategy% (9933)------------------------------
% 0.21/0.55  % (9933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9933)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9933)Memory used [KB]: 10746
% 0.21/0.55  % (9933)Time elapsed: 0.127 s
% 0.21/0.55  % (9933)------------------------------
% 0.21/0.55  % (9933)------------------------------
% 0.21/0.56  % (9927)Refutation not found, incomplete strategy% (9927)------------------------------
% 0.21/0.56  % (9927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9927)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9927)Memory used [KB]: 11001
% 0.21/0.56  % (9927)Time elapsed: 0.153 s
% 0.21/0.56  % (9927)------------------------------
% 0.21/0.56  % (9927)------------------------------
% 0.21/0.56  % (9945)Refutation not found, incomplete strategy% (9945)------------------------------
% 0.21/0.56  % (9945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9945)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9945)Memory used [KB]: 11001
% 0.21/0.56  % (9945)Time elapsed: 0.153 s
% 0.21/0.56  % (9945)------------------------------
% 0.21/0.56  % (9945)------------------------------
% 0.21/0.56  % (9936)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.58  % (9944)Refutation not found, incomplete strategy% (9944)------------------------------
% 0.21/0.58  % (9944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9944)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (9944)Memory used [KB]: 6268
% 0.21/0.58  % (9944)Time elapsed: 0.156 s
% 0.21/0.58  % (9944)------------------------------
% 0.21/0.58  % (9944)------------------------------
% 0.21/0.58  % (9928)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.05/0.63  % (9940)Refutation found. Thanks to Tanya!
% 2.05/0.63  % SZS status Theorem for theBenchmark
% 2.05/0.63  % SZS output start Proof for theBenchmark
% 2.05/0.63  fof(f1382,plain,(
% 2.05/0.63    $false),
% 2.05/0.63    inference(avatar_sat_refutation,[],[f102,f107,f112,f121,f124,f207,f299,f457,f496,f499,f504,f597,f601,f611,f1209,f1289,f1345,f1380,f1381])).
% 2.05/0.63  fof(f1381,plain,(
% 2.05/0.63    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.05/0.63    introduced(theory_tautology_sat_conflict,[])).
% 2.05/0.63  fof(f1380,plain,(
% 2.05/0.63    ~spl2_2 | ~spl2_3 | spl2_30 | ~spl2_49),
% 2.05/0.63    inference(avatar_split_clause,[],[f1372,f1342,f608,f109,f104])).
% 2.05/0.63  fof(f104,plain,(
% 2.05/0.63    spl2_2 <=> l1_pre_topc(sK0)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.05/0.63  fof(f109,plain,(
% 2.05/0.63    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.05/0.63  fof(f608,plain,(
% 2.05/0.63    spl2_30 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 2.05/0.63  fof(f1342,plain,(
% 2.05/0.63    spl2_49 <=> sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 2.05/0.63  fof(f1372,plain,(
% 2.05/0.63    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_49),
% 2.05/0.63    inference(superposition,[],[f1344,f349])).
% 2.05/0.63  fof(f349,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f346])).
% 2.05/0.63  fof(f346,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k5_xboole_0(X1,k3_xboole_0(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.63    inference(superposition,[],[f91,f69])).
% 2.05/0.63  fof(f69,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f39])).
% 2.05/0.63  fof(f39,plain,(
% 2.05/0.63    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f31])).
% 2.05/0.63  fof(f31,axiom,(
% 2.05/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.05/0.63  fof(f91,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f66,f89])).
% 2.05/0.63  fof(f89,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f3])).
% 2.05/0.63  fof(f3,axiom,(
% 2.05/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.05/0.63  fof(f66,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f36])).
% 2.05/0.63  fof(f36,plain,(
% 2.05/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f21])).
% 2.05/0.63  fof(f21,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.05/0.63  fof(f1344,plain,(
% 2.05/0.63    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_49),
% 2.05/0.63    inference(avatar_component_clause,[],[f1342])).
% 2.05/0.63  fof(f1345,plain,(
% 2.05/0.63    ~spl2_18 | spl2_49 | ~spl2_20),
% 2.05/0.63    inference(avatar_split_clause,[],[f1303,f493,f1342,f485])).
% 2.05/0.63  fof(f485,plain,(
% 2.05/0.63    spl2_18 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.05/0.63  fof(f493,plain,(
% 2.05/0.63    spl2_20 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 2.05/0.63  fof(f1303,plain,(
% 2.05/0.63    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_20),
% 2.05/0.63    inference(superposition,[],[f961,f495])).
% 2.05/0.63  fof(f495,plain,(
% 2.05/0.63    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_20),
% 2.05/0.63    inference(avatar_component_clause,[],[f493])).
% 2.05/0.63  fof(f961,plain,(
% 2.05/0.63    ( ! [X10,X11] : (k5_xboole_0(X11,k3_xboole_0(X11,k3_subset_1(X10,X11))) = X11 | ~m1_subset_1(X11,k1_zfmisc_1(X10))) )),
% 2.05/0.63    inference(duplicate_literal_removal,[],[f960])).
% 2.05/0.63  fof(f960,plain,(
% 2.05/0.63    ( ! [X10,X11] : (k5_xboole_0(X11,k3_xboole_0(X11,k3_subset_1(X10,X11))) = X11 | ~m1_subset_1(X11,k1_zfmisc_1(X10)) | ~m1_subset_1(X11,k1_zfmisc_1(X10))) )),
% 2.05/0.63    inference(superposition,[],[f91,f936])).
% 2.05/0.63  fof(f936,plain,(
% 2.05/0.63    ( ! [X4,X5] : (k7_subset_1(X4,X5,k3_subset_1(X4,X5)) = X5 | ~m1_subset_1(X5,k1_zfmisc_1(X4))) )),
% 2.05/0.63    inference(global_subsumption,[],[f83,f932])).
% 2.05/0.64  fof(f932,plain,(
% 2.05/0.64    ( ! [X4,X5] : (k7_subset_1(X4,X5,k3_subset_1(X4,X5)) = X5 | ~m1_subset_1(k3_subset_1(X4,X5),k1_zfmisc_1(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(X4))) )),
% 2.05/0.64    inference(duplicate_literal_removal,[],[f905])).
% 2.05/0.64  fof(f905,plain,(
% 2.05/0.64    ( ! [X4,X5] : (k7_subset_1(X4,X5,k3_subset_1(X4,X5)) = X5 | ~m1_subset_1(k3_subset_1(X4,X5),k1_zfmisc_1(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(X4))) )),
% 2.05/0.64    inference(superposition,[],[f365,f82])).
% 2.05/0.64  fof(f82,plain,(
% 2.05/0.64    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.64    inference(cnf_transformation,[],[f50])).
% 2.05/0.64  fof(f50,plain,(
% 2.05/0.64    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.64    inference(ennf_transformation,[],[f17])).
% 2.05/0.64  fof(f17,axiom,(
% 2.05/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.05/0.64  fof(f365,plain,(
% 2.05/0.64    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.05/0.64    inference(condensation,[],[f364])).
% 2.05/0.64  fof(f364,plain,(
% 2.05/0.64    ( ! [X2,X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.05/0.64    inference(superposition,[],[f81,f67])).
% 2.05/0.64  fof(f67,plain,(
% 2.05/0.64    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.64    inference(cnf_transformation,[],[f37])).
% 2.05/0.64  fof(f37,plain,(
% 2.05/0.64    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.64    inference(ennf_transformation,[],[f22])).
% 2.05/0.64  fof(f22,axiom,(
% 2.05/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 2.05/0.64  fof(f81,plain,(
% 2.05/0.64    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.05/0.64    inference(cnf_transformation,[],[f49])).
% 2.05/0.64  fof(f49,plain,(
% 2.05/0.64    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.05/0.64    inference(ennf_transformation,[],[f16])).
% 2.05/0.64  fof(f16,axiom,(
% 2.05/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 2.05/0.64  fof(f83,plain,(
% 2.05/0.64    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.64    inference(cnf_transformation,[],[f51])).
% 2.05/0.64  fof(f51,plain,(
% 2.05/0.64    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.64    inference(ennf_transformation,[],[f14])).
% 2.05/0.64  fof(f14,axiom,(
% 2.05/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.05/0.64  fof(f1289,plain,(
% 2.05/0.64    ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_30),
% 2.05/0.64    inference(avatar_split_clause,[],[f1224,f608,f118,f109,f104])).
% 2.05/0.64  fof(f118,plain,(
% 2.05/0.64    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.05/0.64  fof(f1224,plain,(
% 2.05/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_30),
% 2.05/0.64    inference(superposition,[],[f68,f610])).
% 2.05/0.64  fof(f610,plain,(
% 2.05/0.64    sK1 = k1_tops_1(sK0,sK1) | ~spl2_30),
% 2.05/0.64    inference(avatar_component_clause,[],[f608])).
% 2.05/0.64  fof(f68,plain,(
% 2.05/0.64    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f38])).
% 2.05/0.64  fof(f38,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(ennf_transformation,[],[f28])).
% 2.05/0.64  fof(f28,axiom,(
% 2.05/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.05/0.64  fof(f1209,plain,(
% 2.05/0.64    ~spl2_2 | ~spl2_3 | spl2_29),
% 2.05/0.64    inference(avatar_contradiction_clause,[],[f1200])).
% 2.05/0.64  fof(f1200,plain,(
% 2.05/0.64    $false | (~spl2_2 | ~spl2_3 | spl2_29)),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f106,f606,f111,f1056])).
% 2.05/0.64  fof(f1056,plain,(
% 2.05/0.64    ( ! [X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X11))) | r1_tarski(k1_tops_1(X11,X10),X10) | ~l1_pre_topc(X11)) )),
% 2.05/0.64    inference(superposition,[],[f1038,f349])).
% 2.05/0.64  fof(f1038,plain,(
% 2.05/0.64    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.05/0.64    inference(resolution,[],[f895,f87])).
% 2.05/0.64  fof(f87,plain,(
% 2.05/0.64    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f4])).
% 2.05/0.64  fof(f4,axiom,(
% 2.05/0.64    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.05/0.64  fof(f895,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(X0,k3_xboole_0(X0,X1)),X0) | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.05/0.64    inference(resolution,[],[f777,f76])).
% 2.05/0.64  fof(f76,plain,(
% 2.05/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f58])).
% 2.05/0.64  fof(f58,plain,(
% 2.05/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.05/0.64    inference(nnf_transformation,[],[f24])).
% 2.05/0.64  fof(f24,axiom,(
% 2.05/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.05/0.64  fof(f777,plain,(
% 2.05/0.64    ( ! [X6,X7] : (~m1_subset_1(k3_xboole_0(X6,k3_xboole_0(X6,X7)),k1_zfmisc_1(X6)) | r1_tarski(k5_xboole_0(X6,k3_xboole_0(X6,X7)),X6)) )),
% 2.05/0.64    inference(superposition,[],[f552,f93])).
% 2.05/0.64  fof(f93,plain,(
% 2.05/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.05/0.64    inference(definition_unfolding,[],[f78,f89,f89])).
% 2.05/0.64  fof(f78,plain,(
% 2.05/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.05/0.64    inference(cnf_transformation,[],[f8])).
% 2.05/0.64  fof(f8,axiom,(
% 2.05/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.05/0.64  fof(f552,plain,(
% 2.05/0.64    ( ! [X8,X7] : (r1_tarski(k5_xboole_0(X7,k3_xboole_0(X7,X8)),X7) | ~m1_subset_1(k3_xboole_0(X7,X8),k1_zfmisc_1(X7))) )),
% 2.05/0.64    inference(duplicate_literal_removal,[],[f540])).
% 2.05/0.64  fof(f540,plain,(
% 2.05/0.64    ( ! [X8,X7] : (r1_tarski(k5_xboole_0(X7,k3_xboole_0(X7,X8)),X7) | ~m1_subset_1(k3_xboole_0(X7,X8),k1_zfmisc_1(X7)) | ~m1_subset_1(k3_xboole_0(X7,X8),k1_zfmisc_1(X7))) )),
% 2.05/0.64    inference(superposition,[],[f160,f238])).
% 2.05/0.64  fof(f238,plain,(
% 2.05/0.64    ( ! [X2,X3] : (k3_subset_1(X2,k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) | ~m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X2))) )),
% 2.05/0.64    inference(superposition,[],[f93,f92])).
% 2.05/0.64  fof(f92,plain,(
% 2.05/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.64    inference(definition_unfolding,[],[f77,f89])).
% 2.05/0.64  fof(f77,plain,(
% 2.05/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.64    inference(cnf_transformation,[],[f48])).
% 2.05/0.64  fof(f48,plain,(
% 2.05/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.64    inference(ennf_transformation,[],[f13])).
% 2.05/0.64  fof(f13,axiom,(
% 2.05/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.05/0.64  fof(f160,plain,(
% 2.05/0.64    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X1,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.05/0.64    inference(resolution,[],[f83,f75])).
% 2.05/0.64  fof(f75,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f58])).
% 2.05/0.64  fof(f111,plain,(
% 2.05/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 2.05/0.64    inference(avatar_component_clause,[],[f109])).
% 2.05/0.64  fof(f606,plain,(
% 2.05/0.64    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl2_29),
% 2.05/0.64    inference(avatar_component_clause,[],[f604])).
% 2.05/0.64  fof(f604,plain,(
% 2.05/0.64    spl2_29 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 2.05/0.64  fof(f106,plain,(
% 2.05/0.64    l1_pre_topc(sK0) | ~spl2_2),
% 2.05/0.64    inference(avatar_component_clause,[],[f104])).
% 2.05/0.64  fof(f611,plain,(
% 2.05/0.64    ~spl2_29 | spl2_30 | ~spl2_27),
% 2.05/0.64    inference(avatar_split_clause,[],[f602,f590,f608,f604])).
% 2.05/0.64  fof(f590,plain,(
% 2.05/0.64    spl2_27 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 2.05/0.64  fof(f602,plain,(
% 2.05/0.64    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_27),
% 2.05/0.64    inference(resolution,[],[f592,f86])).
% 2.05/0.64  fof(f86,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f60])).
% 2.05/0.64  fof(f60,plain,(
% 2.05/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.64    inference(flattening,[],[f59])).
% 2.05/0.64  fof(f59,plain,(
% 2.05/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.05/0.64    inference(nnf_transformation,[],[f2])).
% 2.05/0.64  fof(f2,axiom,(
% 2.05/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.05/0.64  fof(f592,plain,(
% 2.05/0.64    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl2_27),
% 2.05/0.64    inference(avatar_component_clause,[],[f590])).
% 2.05/0.64  fof(f601,plain,(
% 2.05/0.64    spl2_28),
% 2.05/0.64    inference(avatar_contradiction_clause,[],[f598])).
% 2.05/0.64  fof(f598,plain,(
% 2.05/0.64    $false | spl2_28),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f96,f596])).
% 2.05/0.64  fof(f596,plain,(
% 2.05/0.64    ~r1_tarski(sK1,sK1) | spl2_28),
% 2.05/0.64    inference(avatar_component_clause,[],[f594])).
% 2.05/0.64  fof(f594,plain,(
% 2.05/0.64    spl2_28 <=> r1_tarski(sK1,sK1)),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 2.05/0.64  fof(f96,plain,(
% 2.05/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.05/0.64    inference(equality_resolution,[],[f85])).
% 2.05/0.64  fof(f85,plain,(
% 2.05/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.05/0.64    inference(cnf_transformation,[],[f60])).
% 2.05/0.64  fof(f597,plain,(
% 2.05/0.64    ~spl2_4 | spl2_27 | ~spl2_28 | ~spl2_3 | ~spl2_17),
% 2.05/0.64    inference(avatar_split_clause,[],[f462,f455,f109,f594,f590,f114])).
% 2.05/0.64  fof(f114,plain,(
% 2.05/0.64    spl2_4 <=> v3_pre_topc(sK1,sK0)),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.05/0.64  fof(f455,plain,(
% 2.05/0.64    spl2_17 <=> ! [X11] : (~r1_tarski(X11,sK1) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X11,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X11,sK0))),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 2.05/0.64  fof(f462,plain,(
% 2.05/0.64    ~r1_tarski(sK1,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_17)),
% 2.05/0.64    inference(resolution,[],[f456,f111])).
% 2.05/0.64  fof(f456,plain,(
% 2.05/0.64    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X11,sK1) | r1_tarski(X11,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X11,sK0)) ) | ~spl2_17),
% 2.05/0.64    inference(avatar_component_clause,[],[f455])).
% 2.05/0.64  fof(f504,plain,(
% 2.05/0.64    ~spl2_2 | ~spl2_3 | spl2_19),
% 2.05/0.64    inference(avatar_contradiction_clause,[],[f501])).
% 2.05/0.64  fof(f501,plain,(
% 2.05/0.64    $false | (~spl2_2 | ~spl2_3 | spl2_19)),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f106,f111,f491,f70])).
% 2.05/0.64  fof(f70,plain,(
% 2.05/0.64    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f41])).
% 2.05/0.64  fof(f41,plain,(
% 2.05/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(flattening,[],[f40])).
% 2.05/0.64  fof(f40,plain,(
% 2.05/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.05/0.64    inference(ennf_transformation,[],[f25])).
% 2.05/0.64  fof(f25,axiom,(
% 2.05/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.05/0.64  fof(f491,plain,(
% 2.05/0.64    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_19),
% 2.05/0.64    inference(avatar_component_clause,[],[f489])).
% 2.05/0.64  fof(f489,plain,(
% 2.05/0.64    spl2_19 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 2.05/0.64  fof(f499,plain,(
% 2.05/0.64    ~spl2_13 | spl2_18),
% 2.05/0.64    inference(avatar_contradiction_clause,[],[f497])).
% 2.05/0.64  fof(f497,plain,(
% 2.05/0.64    $false | (~spl2_13 | spl2_18)),
% 2.05/0.64    inference(unit_resulting_resolution,[],[f206,f487,f76])).
% 2.05/0.64  fof(f487,plain,(
% 2.05/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_18),
% 2.05/0.64    inference(avatar_component_clause,[],[f485])).
% 2.05/0.64  fof(f206,plain,(
% 2.05/0.64    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_13),
% 2.05/0.64    inference(avatar_component_clause,[],[f204])).
% 2.05/0.64  fof(f204,plain,(
% 2.05/0.64    spl2_13 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 2.05/0.64  fof(f496,plain,(
% 2.05/0.64    ~spl2_18 | ~spl2_19 | spl2_20 | ~spl2_5),
% 2.05/0.64    inference(avatar_split_clause,[],[f427,f118,f493,f489,f485])).
% 2.05/0.64  fof(f427,plain,(
% 2.05/0.64    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_5),
% 2.05/0.64    inference(superposition,[],[f320,f120])).
% 2.05/0.64  fof(f120,plain,(
% 2.05/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_5),
% 2.05/0.64    inference(avatar_component_clause,[],[f118])).
% 2.05/0.64  fof(f320,plain,(
% 2.05/0.64    ( ! [X6,X8,X7] : (k3_subset_1(X6,X7) = k7_subset_1(X8,X6,X7) | ~m1_subset_1(X6,k1_zfmisc_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(X6))) )),
% 2.05/0.64    inference(superposition,[],[f91,f92])).
% 2.05/0.64  fof(f457,plain,(
% 2.05/0.64    ~spl2_2 | spl2_17 | ~spl2_3),
% 2.05/0.64    inference(avatar_split_clause,[],[f452,f109,f455,f104])).
% 2.05/0.64  fof(f452,plain,(
% 2.05/0.64    ( ! [X11] : (~r1_tarski(X11,sK1) | ~v3_pre_topc(X11,sK0) | r1_tarski(X11,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_3),
% 2.05/0.64    inference(resolution,[],[f74,f111])).
% 2.05/0.64  fof(f74,plain,(
% 2.05/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f47])).
% 2.05/0.64  fof(f47,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(flattening,[],[f46])).
% 2.05/0.64  fof(f46,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(ennf_transformation,[],[f29])).
% 2.05/0.64  fof(f29,axiom,(
% 2.05/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 2.05/0.64  fof(f299,plain,(
% 2.05/0.64    ~spl2_1 | ~spl2_2 | spl2_16 | ~spl2_3),
% 2.05/0.64    inference(avatar_split_clause,[],[f293,f109,f296,f104,f99])).
% 2.05/0.64  fof(f99,plain,(
% 2.05/0.64    spl2_1 <=> v2_pre_topc(sK0)),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.05/0.64  fof(f296,plain,(
% 2.05/0.64    spl2_16 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.05/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 2.05/0.64  fof(f293,plain,(
% 2.05/0.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 2.05/0.64    inference(resolution,[],[f73,f111])).
% 2.05/0.64  fof(f73,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f45])).
% 2.05/0.64  fof(f45,plain,(
% 2.05/0.64    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.05/0.64    inference(flattening,[],[f44])).
% 2.05/0.64  fof(f44,plain,(
% 2.05/0.64    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.05/0.64    inference(ennf_transformation,[],[f27])).
% 2.05/0.64  fof(f27,axiom,(
% 2.05/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.05/0.64  fof(f207,plain,(
% 2.05/0.64    ~spl2_2 | spl2_13 | ~spl2_3),
% 2.05/0.64    inference(avatar_split_clause,[],[f202,f109,f204,f104])).
% 2.05/0.64  fof(f202,plain,(
% 2.05/0.64    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 2.05/0.64    inference(resolution,[],[f71,f111])).
% 2.05/0.64  fof(f71,plain,(
% 2.05/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.05/0.64    inference(cnf_transformation,[],[f42])).
% 2.05/0.64  fof(f42,plain,(
% 2.05/0.64    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.05/0.64    inference(ennf_transformation,[],[f26])).
% 2.05/0.64  fof(f26,axiom,(
% 2.05/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.05/0.64  fof(f124,plain,(
% 2.05/0.64    ~spl2_4 | ~spl2_5),
% 2.05/0.64    inference(avatar_split_clause,[],[f123,f118,f114])).
% 2.05/0.64  fof(f123,plain,(
% 2.05/0.64    ~v3_pre_topc(sK1,sK0) | ~spl2_5),
% 2.05/0.64    inference(trivial_inequality_removal,[],[f122])).
% 2.05/0.64  fof(f122,plain,(
% 2.05/0.64    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl2_5),
% 2.05/0.64    inference(forward_demodulation,[],[f65,f120])).
% 2.05/0.64  fof(f65,plain,(
% 2.05/0.64    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.05/0.64    inference(cnf_transformation,[],[f57])).
% 2.05/0.64  fof(f57,plain,(
% 2.05/0.64    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.05/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).
% 2.05/0.64  fof(f55,plain,(
% 2.05/0.64    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.05/0.64    introduced(choice_axiom,[])).
% 2.05/0.64  fof(f56,plain,(
% 2.05/0.64    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.05/0.64    introduced(choice_axiom,[])).
% 2.05/0.64  fof(f54,plain,(
% 2.05/0.64    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.05/0.64    inference(flattening,[],[f53])).
% 2.05/0.64  fof(f53,plain,(
% 2.05/0.64    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.05/0.64    inference(nnf_transformation,[],[f35])).
% 2.05/0.64  fof(f35,plain,(
% 2.05/0.64    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.05/0.64    inference(flattening,[],[f34])).
% 2.05/0.64  fof(f34,plain,(
% 2.05/0.64    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.05/0.64    inference(ennf_transformation,[],[f33])).
% 2.05/0.64  fof(f33,negated_conjecture,(
% 2.05/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.05/0.64    inference(negated_conjecture,[],[f32])).
% 2.05/0.64  fof(f32,conjecture,(
% 2.05/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.05/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.05/0.64  fof(f121,plain,(
% 2.05/0.64    spl2_4 | spl2_5),
% 2.05/0.64    inference(avatar_split_clause,[],[f64,f118,f114])).
% 2.05/0.64  fof(f64,plain,(
% 2.05/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.05/0.64    inference(cnf_transformation,[],[f57])).
% 2.05/0.64  fof(f112,plain,(
% 2.05/0.64    spl2_3),
% 2.05/0.64    inference(avatar_split_clause,[],[f63,f109])).
% 2.05/0.64  fof(f63,plain,(
% 2.05/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.05/0.64    inference(cnf_transformation,[],[f57])).
% 2.05/0.64  fof(f107,plain,(
% 2.05/0.64    spl2_2),
% 2.05/0.64    inference(avatar_split_clause,[],[f62,f104])).
% 2.05/0.64  fof(f62,plain,(
% 2.05/0.64    l1_pre_topc(sK0)),
% 2.05/0.64    inference(cnf_transformation,[],[f57])).
% 2.05/0.64  fof(f102,plain,(
% 2.05/0.64    spl2_1),
% 2.05/0.64    inference(avatar_split_clause,[],[f61,f99])).
% 2.05/0.64  fof(f61,plain,(
% 2.05/0.64    v2_pre_topc(sK0)),
% 2.05/0.64    inference(cnf_transformation,[],[f57])).
% 2.05/0.64  % SZS output end Proof for theBenchmark
% 2.05/0.64  % (9940)------------------------------
% 2.05/0.64  % (9940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.64  % (9940)Termination reason: Refutation
% 2.05/0.64  
% 2.05/0.64  % (9940)Memory used [KB]: 11769
% 2.05/0.64  % (9940)Time elapsed: 0.228 s
% 2.05/0.64  % (9940)------------------------------
% 2.05/0.64  % (9940)------------------------------
% 2.05/0.64  % (9915)Success in time 0.274 s
%------------------------------------------------------------------------------
