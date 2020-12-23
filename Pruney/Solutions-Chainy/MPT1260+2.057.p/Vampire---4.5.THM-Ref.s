%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:42 EST 2020

% Result     : Theorem 4.35s
% Output     : Refutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 381 expanded)
%              Number of leaves         :   35 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :  589 (1192 expanded)
%              Number of equality atoms :  115 ( 293 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7546,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f79,f84,f89,f94,f101,f108,f114,f147,f176,f197,f203,f278,f5031,f6978,f7182,f7494,f7505,f7539])).

fof(f7539,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f7538])).

fof(f7538,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f7537,f73])).

fof(f73,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f7537,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f7536,f83])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f7536,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f7535,f88])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f7535,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f7533,f93])).

fof(f93,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f7533,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(trivial_inequality_removal,[],[f7522])).

fof(f7522,plain,
    ( sK1 != sK1
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | ~ spl2_7
    | ~ spl2_13 ),
    inference(superposition,[],[f100,f195])).

fof(f195,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl2_13
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f100,plain,
    ( ! [X2,X0] :
        ( k1_tops_1(X0,X2) != X2
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_7
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X2) != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f7505,plain,
    ( ~ spl2_57
    | spl2_13
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f7504,f86,f81,f193,f1149])).

fof(f1149,plain,
    ( spl2_57
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f7504,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1312,f88])).

fof(f1312,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f449,f83])).

fof(f449,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | k1_tops_1(X9,X8) = X8
      | ~ r1_tarski(X8,k1_tops_1(X9,X8))
      | ~ l1_pre_topc(X9) ) ),
    inference(superposition,[],[f126,f219])).

fof(f219,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f48,f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(X1,X2))
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f51,f66])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f7494,plain,
    ( spl2_209
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_146 ),
    inference(avatar_split_clause,[],[f7493,f5028,f161,f81,f6795])).

fof(f6795,plain,
    ( spl2_209
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_209])])).

fof(f161,plain,
    ( spl2_11
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f5028,plain,
    ( spl2_146
  <=> r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_146])])).

fof(f7493,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_146 ),
    inference(subsumption_resolution,[],[f7492,f83])).

fof(f7492,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_11
    | ~ spl2_146 ),
    inference(subsumption_resolution,[],[f7488,f163])).

fof(f163,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f7488,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_146 ),
    inference(resolution,[],[f5030,f1469])).

fof(f1469,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X4,k3_subset_1(X3,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | k4_xboole_0(X4,X5) = X4 ) ),
    inference(duplicate_literal_removal,[],[f1460])).

fof(f1460,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(X4,X5) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ r1_tarski(X4,k3_subset_1(X3,X5)) ) ),
    inference(superposition,[],[f48,f485])).

fof(f485,plain,(
    ! [X6,X8,X7] :
      ( k7_subset_1(X7,X6,X8) = X6
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | ~ r1_tarski(X6,k3_subset_1(X7,X8)) ) ),
    inference(superposition,[],[f223,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f223,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X4,k3_subset_1(X3,X5)) = k7_subset_1(X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f221,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f221,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X4,k3_subset_1(X3,X5)) = k7_subset_1(X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X5),k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f58,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f5030,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_146 ),
    inference(avatar_component_clause,[],[f5028])).

fof(f7182,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_57
    | ~ spl2_214 ),
    inference(avatar_contradiction_clause,[],[f7181])).

fof(f7181,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_57
    | ~ spl2_214 ),
    inference(subsumption_resolution,[],[f7180,f88])).

fof(f7180,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_57
    | ~ spl2_214 ),
    inference(subsumption_resolution,[],[f7179,f83])).

fof(f7179,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_57
    | ~ spl2_214 ),
    inference(subsumption_resolution,[],[f7177,f1151])).

fof(f1151,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl2_57 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f7177,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_214 ),
    inference(trivial_inequality_removal,[],[f7154])).

fof(f7154,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_214 ),
    inference(superposition,[],[f1362,f6921])).

fof(f6921,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_214 ),
    inference(avatar_component_clause,[],[f6919])).

fof(f6919,plain,
    ( spl2_214
  <=> k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_214])])).

fof(f1362,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k3_xboole_0(X2,k2_tops_1(X3,X2))
      | r1_tarski(X2,k1_tops_1(X3,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f64,f445])).

fof(f445,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_tops_1(X1,X0)) = k4_xboole_0(X0,k1_tops_1(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f53,f219])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f6978,plain,
    ( spl2_214
    | ~ spl2_209 ),
    inference(avatar_split_clause,[],[f6977,f6795,f6919])).

fof(f6977,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_209 ),
    inference(forward_demodulation,[],[f6976,f569])).

fof(f569,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f129,f306])).

fof(f306,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f297,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f297,plain,(
    ! [X1] :
      ( k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f129,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f129,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f53,f67])).

fof(f67,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f6976,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_209 ),
    inference(forward_demodulation,[],[f6975,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6975,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_209 ),
    inference(forward_demodulation,[],[f6912,f590])).

fof(f590,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f583,f67])).

fof(f583,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f53,f569])).

fof(f6912,plain,
    ( k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl2_209 ),
    inference(superposition,[],[f2231,f6797])).

fof(f6797,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_209 ),
    inference(avatar_component_clause,[],[f6795])).

fof(f2231,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f421,f814])).

fof(f814,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k3_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(subsumption_resolution,[],[f788,f66])).

fof(f788,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(X7,X8) = k3_xboole_0(X7,k3_xboole_0(X7,X8))
      | ~ r1_tarski(k4_xboole_0(X7,X8),X7) ) ),
    inference(superposition,[],[f415,f53])).

fof(f415,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f131,f115])).

fof(f115,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f52,f54])).

fof(f131,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f53,f53])).

fof(f421,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f53,f131])).

fof(f5031,plain,
    ( spl2_146
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f5026,f157,f81,f75,f5028])).

fof(f75,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f157,plain,
    ( spl2_10
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f5026,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f5025,f158])).

fof(f158,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f5025,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f5008,f83])).

fof(f5008,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f567,f76])).

fof(f76,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f567,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(k7_subset_1(X9,X8,X10),k3_subset_1(X9,X10))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9)) ) ),
    inference(superposition,[],[f140,f223])).

fof(f140,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f135,f54])).

fof(f135,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f66,f53])).

fof(f278,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f276,f88])).

fof(f276,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f275,f83])).

fof(f275,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f272,f77])).

fof(f77,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f272,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_13 ),
    inference(superposition,[],[f55,f195])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f203,plain,
    ( ~ spl2_10
    | spl2_11
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f200,f75,f161,f157])).

fof(f200,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f57,f76])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f197,plain,
    ( ~ spl2_1
    | spl2_13
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f190,f106,f86,f81,f193,f71])).

fof(f106,plain,
    ( spl2_9
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f190,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f188,f88])).

fof(f188,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f107,f83])).

fof(f107,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f176,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10 ),
    inference(subsumption_resolution,[],[f174,f88])).

fof(f174,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_10 ),
    inference(subsumption_resolution,[],[f172,f83])).

fof(f172,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_10 ),
    inference(resolution,[],[f59,f159])).

fof(f159,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f147,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f145,f88])).

fof(f145,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f143,f93])).

fof(f143,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f104,f83])).

fof(f104,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_8
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f114,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f111,f88])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(resolution,[],[f97,f83])).

fof(f97,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_6
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f108,plain,
    ( spl2_8
    | spl2_9 ),
    inference(avatar_split_clause,[],[f60,f106,f103])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f101,plain,
    ( spl2_6
    | spl2_7 ),
    inference(avatar_split_clause,[],[f61,f99,f96])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f43,f91])).

fof(f43,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

% (18099)Time limit reached!
% (18099)------------------------------
% (18099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18099)Termination reason: Time limit

% (18099)Memory used [KB]: 13688
% (18099)Time elapsed: 0.516 s
% (18099)------------------------------
% (18099)------------------------------
fof(f37,plain,
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

fof(f38,plain,
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

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f89,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f81])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f46,f75,f71])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f47,f75,f71])).

fof(f47,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (18112)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (18098)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (18121)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.51  % (18108)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (18107)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (18097)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (18121)Refutation not found, incomplete strategy% (18121)------------------------------
% 0.21/0.51  % (18121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18121)Memory used [KB]: 10746
% 0.21/0.51  % (18121)Time elapsed: 0.101 s
% 0.21/0.51  % (18121)------------------------------
% 0.21/0.51  % (18121)------------------------------
% 0.21/0.52  % (18099)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (18101)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (18105)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (18100)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (18114)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (18103)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (18103)Refutation not found, incomplete strategy% (18103)------------------------------
% 0.21/0.53  % (18103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18103)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18103)Memory used [KB]: 10746
% 0.21/0.53  % (18103)Time elapsed: 0.115 s
% 0.21/0.53  % (18103)------------------------------
% 0.21/0.53  % (18103)------------------------------
% 0.21/0.53  % (18115)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (18094)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (18122)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (18096)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (18095)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (18122)Refutation not found, incomplete strategy% (18122)------------------------------
% 0.21/0.54  % (18122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18122)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18122)Memory used [KB]: 1663
% 0.21/0.54  % (18122)Time elapsed: 0.128 s
% 0.21/0.54  % (18122)------------------------------
% 0.21/0.54  % (18122)------------------------------
% 0.21/0.54  % (18093)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (18104)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (18102)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (18120)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (18113)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (18118)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (18116)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (18117)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (18110)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (18106)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (18119)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (18109)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (18109)Refutation not found, incomplete strategy% (18109)------------------------------
% 0.21/0.56  % (18109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18109)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18109)Memory used [KB]: 10618
% 0.21/0.56  % (18109)Time elapsed: 0.151 s
% 0.21/0.56  % (18109)------------------------------
% 0.21/0.56  % (18109)------------------------------
% 0.21/0.56  % (18111)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.03/0.66  % (18181)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.03/0.67  % (18192)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.03/0.68  % (18200)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.03/0.69  % (18213)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.34/0.82  % (18095)Time limit reached!
% 3.34/0.82  % (18095)------------------------------
% 3.34/0.82  % (18095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.83  % (18117)Time limit reached!
% 3.34/0.83  % (18117)------------------------------
% 3.34/0.83  % (18117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.83  % (18117)Termination reason: Time limit
% 3.34/0.83  % (18117)Termination phase: Saturation
% 3.34/0.83  
% 3.34/0.83  % (18117)Memory used [KB]: 13304
% 3.34/0.83  % (18117)Time elapsed: 0.400 s
% 3.34/0.83  % (18117)------------------------------
% 3.34/0.83  % (18117)------------------------------
% 3.34/0.83  % (18095)Termination reason: Time limit
% 3.34/0.83  
% 3.34/0.83  % (18095)Memory used [KB]: 6652
% 3.34/0.83  % (18095)Time elapsed: 0.407 s
% 3.34/0.83  % (18095)------------------------------
% 3.34/0.83  % (18095)------------------------------
% 4.35/0.93  % (18114)Refutation found. Thanks to Tanya!
% 4.35/0.93  % SZS status Theorem for theBenchmark
% 4.35/0.93  % SZS output start Proof for theBenchmark
% 4.35/0.93  fof(f7546,plain,(
% 4.35/0.93    $false),
% 4.35/0.93    inference(avatar_sat_refutation,[],[f78,f79,f84,f89,f94,f101,f108,f114,f147,f176,f197,f203,f278,f5031,f6978,f7182,f7494,f7505,f7539])).
% 4.35/0.93  fof(f7539,plain,(
% 4.35/0.93    spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_13),
% 4.35/0.93    inference(avatar_contradiction_clause,[],[f7538])).
% 4.35/0.93  fof(f7538,plain,(
% 4.35/0.93    $false | (spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_13)),
% 4.35/0.93    inference(subsumption_resolution,[],[f7537,f73])).
% 4.35/0.93  fof(f73,plain,(
% 4.35/0.93    ~v3_pre_topc(sK1,sK0) | spl2_1),
% 4.35/0.93    inference(avatar_component_clause,[],[f71])).
% 4.35/0.93  fof(f71,plain,(
% 4.35/0.93    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 4.35/0.93  fof(f7537,plain,(
% 4.35/0.93    v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_13)),
% 4.35/0.93    inference(subsumption_resolution,[],[f7536,f83])).
% 4.35/0.93  fof(f83,plain,(
% 4.35/0.93    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 4.35/0.93    inference(avatar_component_clause,[],[f81])).
% 4.35/0.93  fof(f81,plain,(
% 4.35/0.93    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 4.35/0.93  fof(f7536,plain,(
% 4.35/0.93    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_13)),
% 4.35/0.93    inference(subsumption_resolution,[],[f7535,f88])).
% 4.35/0.93  fof(f88,plain,(
% 4.35/0.93    l1_pre_topc(sK0) | ~spl2_4),
% 4.35/0.93    inference(avatar_component_clause,[],[f86])).
% 4.35/0.93  fof(f86,plain,(
% 4.35/0.93    spl2_4 <=> l1_pre_topc(sK0)),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 4.35/0.93  fof(f7535,plain,(
% 4.35/0.93    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl2_5 | ~spl2_7 | ~spl2_13)),
% 4.35/0.93    inference(subsumption_resolution,[],[f7533,f93])).
% 4.35/0.93  fof(f93,plain,(
% 4.35/0.93    v2_pre_topc(sK0) | ~spl2_5),
% 4.35/0.93    inference(avatar_component_clause,[],[f91])).
% 4.35/0.93  fof(f91,plain,(
% 4.35/0.93    spl2_5 <=> v2_pre_topc(sK0)),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 4.35/0.93  fof(f7533,plain,(
% 4.35/0.93    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl2_7 | ~spl2_13)),
% 4.35/0.93    inference(trivial_inequality_removal,[],[f7522])).
% 4.35/0.93  fof(f7522,plain,(
% 4.35/0.93    sK1 != sK1 | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | (~spl2_7 | ~spl2_13)),
% 4.35/0.93    inference(superposition,[],[f100,f195])).
% 4.35/0.93  fof(f195,plain,(
% 4.35/0.93    sK1 = k1_tops_1(sK0,sK1) | ~spl2_13),
% 4.35/0.93    inference(avatar_component_clause,[],[f193])).
% 4.35/0.93  fof(f193,plain,(
% 4.35/0.93    spl2_13 <=> sK1 = k1_tops_1(sK0,sK1)),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 4.35/0.93  fof(f100,plain,(
% 4.35/0.93    ( ! [X2,X0] : (k1_tops_1(X0,X2) != X2 | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) ) | ~spl2_7),
% 4.35/0.93    inference(avatar_component_clause,[],[f99])).
% 4.35/0.93  fof(f99,plain,(
% 4.35/0.93    spl2_7 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2)),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 4.35/0.93  fof(f7505,plain,(
% 4.35/0.93    ~spl2_57 | spl2_13 | ~spl2_3 | ~spl2_4),
% 4.35/0.93    inference(avatar_split_clause,[],[f7504,f86,f81,f193,f1149])).
% 4.35/0.93  fof(f1149,plain,(
% 4.35/0.93    spl2_57 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 4.35/0.93  fof(f7504,plain,(
% 4.35/0.93    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 4.35/0.93    inference(subsumption_resolution,[],[f1312,f88])).
% 4.35/0.93  fof(f1312,plain,(
% 4.35/0.93    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 4.35/0.93    inference(resolution,[],[f449,f83])).
% 4.35/0.93  fof(f449,plain,(
% 4.35/0.93    ( ! [X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | k1_tops_1(X9,X8) = X8 | ~r1_tarski(X8,k1_tops_1(X9,X8)) | ~l1_pre_topc(X9)) )),
% 4.35/0.93    inference(superposition,[],[f126,f219])).
% 4.35/0.93  fof(f219,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.35/0.93    inference(duplicate_literal_removal,[],[f216])).
% 4.35/0.93  fof(f216,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.35/0.93    inference(superposition,[],[f48,f56])).
% 4.35/0.93  fof(f56,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f26])).
% 4.35/0.93  fof(f26,plain,(
% 4.35/0.93    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.35/0.93    inference(ennf_transformation,[],[f18])).
% 4.35/0.93  fof(f18,axiom,(
% 4.35/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 4.35/0.93  fof(f48,plain,(
% 4.35/0.93    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.35/0.93    inference(cnf_transformation,[],[f23])).
% 4.35/0.93  fof(f23,plain,(
% 4.35/0.93    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.35/0.93    inference(ennf_transformation,[],[f11])).
% 4.35/0.93  fof(f11,axiom,(
% 4.35/0.93    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 4.35/0.93  fof(f126,plain,(
% 4.35/0.93    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(X1,X2)) | k4_xboole_0(X1,X2) = X1) )),
% 4.35/0.93    inference(resolution,[],[f51,f66])).
% 4.35/0.93  fof(f66,plain,(
% 4.35/0.93    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f6])).
% 4.35/0.93  fof(f6,axiom,(
% 4.35/0.93    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.35/0.93  fof(f51,plain,(
% 4.35/0.93    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f41])).
% 4.35/0.93  fof(f41,plain,(
% 4.35/0.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.35/0.93    inference(flattening,[],[f40])).
% 4.35/0.93  fof(f40,plain,(
% 4.35/0.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.35/0.93    inference(nnf_transformation,[],[f2])).
% 4.35/0.93  fof(f2,axiom,(
% 4.35/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.35/0.93  fof(f7494,plain,(
% 4.35/0.93    spl2_209 | ~spl2_3 | ~spl2_11 | ~spl2_146),
% 4.35/0.93    inference(avatar_split_clause,[],[f7493,f5028,f161,f81,f6795])).
% 4.35/0.93  fof(f6795,plain,(
% 4.35/0.93    spl2_209 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_209])])).
% 4.35/0.93  fof(f161,plain,(
% 4.35/0.93    spl2_11 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 4.35/0.93  fof(f5028,plain,(
% 4.35/0.93    spl2_146 <=> r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_146])])).
% 4.35/0.93  fof(f7493,plain,(
% 4.35/0.93    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_11 | ~spl2_146)),
% 4.35/0.93    inference(subsumption_resolution,[],[f7492,f83])).
% 4.35/0.93  fof(f7492,plain,(
% 4.35/0.93    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_11 | ~spl2_146)),
% 4.35/0.93    inference(subsumption_resolution,[],[f7488,f163])).
% 4.35/0.93  fof(f163,plain,(
% 4.35/0.93    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_11),
% 4.35/0.93    inference(avatar_component_clause,[],[f161])).
% 4.35/0.93  fof(f7488,plain,(
% 4.35/0.93    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_146),
% 4.35/0.93    inference(resolution,[],[f5030,f1469])).
% 4.35/0.93  fof(f1469,plain,(
% 4.35/0.93    ( ! [X4,X5,X3] : (~r1_tarski(X4,k3_subset_1(X3,X5)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | k4_xboole_0(X4,X5) = X4) )),
% 4.35/0.93    inference(duplicate_literal_removal,[],[f1460])).
% 4.35/0.93  fof(f1460,plain,(
% 4.35/0.93    ( ! [X4,X5,X3] : (k4_xboole_0(X4,X5) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~r1_tarski(X4,k3_subset_1(X3,X5))) )),
% 4.35/0.93    inference(superposition,[],[f48,f485])).
% 4.35/0.93  fof(f485,plain,(
% 4.35/0.93    ( ! [X6,X8,X7] : (k7_subset_1(X7,X6,X8) = X6 | ~m1_subset_1(X8,k1_zfmisc_1(X7)) | ~m1_subset_1(X6,k1_zfmisc_1(X7)) | ~r1_tarski(X6,k3_subset_1(X7,X8))) )),
% 4.35/0.93    inference(superposition,[],[f223,f52])).
% 4.35/0.93  fof(f52,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f24])).
% 4.35/0.93  fof(f24,plain,(
% 4.35/0.93    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.35/0.93    inference(ennf_transformation,[],[f5])).
% 4.35/0.93  fof(f5,axiom,(
% 4.35/0.93    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.35/0.93  fof(f223,plain,(
% 4.35/0.93    ( ! [X4,X5,X3] : (k3_xboole_0(X4,k3_subset_1(X3,X5)) = k7_subset_1(X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3))) )),
% 4.35/0.93    inference(subsumption_resolution,[],[f221,f63])).
% 4.35/0.93  fof(f63,plain,(
% 4.35/0.93    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.35/0.93    inference(cnf_transformation,[],[f34])).
% 4.35/0.93  fof(f34,plain,(
% 4.35/0.93    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.35/0.93    inference(ennf_transformation,[],[f9])).
% 4.35/0.93  fof(f9,axiom,(
% 4.35/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 4.35/0.93  fof(f221,plain,(
% 4.35/0.93    ( ! [X4,X5,X3] : (k3_xboole_0(X4,k3_subset_1(X3,X5)) = k7_subset_1(X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X5),k1_zfmisc_1(X3))) )),
% 4.35/0.93    inference(superposition,[],[f58,f62])).
% 4.35/0.93  fof(f62,plain,(
% 4.35/0.93    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.35/0.93    inference(cnf_transformation,[],[f33])).
% 4.35/0.93  fof(f33,plain,(
% 4.35/0.93    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.35/0.93    inference(ennf_transformation,[],[f12])).
% 4.35/0.93  fof(f12,axiom,(
% 4.35/0.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 4.35/0.93  fof(f58,plain,(
% 4.35/0.93    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.35/0.93    inference(cnf_transformation,[],[f28])).
% 4.35/0.93  fof(f28,plain,(
% 4.35/0.93    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.35/0.93    inference(ennf_transformation,[],[f13])).
% 4.35/0.93  fof(f13,axiom,(
% 4.35/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 4.35/0.93  fof(f5030,plain,(
% 4.35/0.93    r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_146),
% 4.35/0.93    inference(avatar_component_clause,[],[f5028])).
% 4.35/0.93  fof(f7182,plain,(
% 4.35/0.93    ~spl2_3 | ~spl2_4 | spl2_57 | ~spl2_214),
% 4.35/0.93    inference(avatar_contradiction_clause,[],[f7181])).
% 4.35/0.93  fof(f7181,plain,(
% 4.35/0.93    $false | (~spl2_3 | ~spl2_4 | spl2_57 | ~spl2_214)),
% 4.35/0.93    inference(subsumption_resolution,[],[f7180,f88])).
% 4.35/0.93  fof(f7180,plain,(
% 4.35/0.93    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_57 | ~spl2_214)),
% 4.35/0.93    inference(subsumption_resolution,[],[f7179,f83])).
% 4.35/0.93  fof(f7179,plain,(
% 4.35/0.93    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_57 | ~spl2_214)),
% 4.35/0.93    inference(subsumption_resolution,[],[f7177,f1151])).
% 4.35/0.93  fof(f1151,plain,(
% 4.35/0.93    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl2_57),
% 4.35/0.93    inference(avatar_component_clause,[],[f1149])).
% 4.35/0.93  fof(f7177,plain,(
% 4.35/0.93    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_214),
% 4.35/0.93    inference(trivial_inequality_removal,[],[f7154])).
% 4.35/0.93  fof(f7154,plain,(
% 4.35/0.93    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_214),
% 4.35/0.93    inference(superposition,[],[f1362,f6921])).
% 4.35/0.93  fof(f6921,plain,(
% 4.35/0.93    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_214),
% 4.35/0.93    inference(avatar_component_clause,[],[f6919])).
% 4.35/0.93  fof(f6919,plain,(
% 4.35/0.93    spl2_214 <=> k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_214])])).
% 4.35/0.93  fof(f1362,plain,(
% 4.35/0.93    ( ! [X2,X3] : (k1_xboole_0 != k3_xboole_0(X2,k2_tops_1(X3,X2)) | r1_tarski(X2,k1_tops_1(X3,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3)) )),
% 4.35/0.93    inference(superposition,[],[f64,f445])).
% 4.35/0.93  fof(f445,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,k2_tops_1(X1,X0)) = k4_xboole_0(X0,k1_tops_1(X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 4.35/0.93    inference(superposition,[],[f53,f219])).
% 4.35/0.93  fof(f53,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.35/0.93    inference(cnf_transformation,[],[f8])).
% 4.35/0.93  fof(f8,axiom,(
% 4.35/0.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.35/0.93  fof(f64,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f42])).
% 4.35/0.93  fof(f42,plain,(
% 4.35/0.93    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.35/0.93    inference(nnf_transformation,[],[f3])).
% 4.35/0.93  fof(f3,axiom,(
% 4.35/0.93    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.35/0.93  fof(f6978,plain,(
% 4.35/0.93    spl2_214 | ~spl2_209),
% 4.35/0.93    inference(avatar_split_clause,[],[f6977,f6795,f6919])).
% 4.35/0.93  fof(f6977,plain,(
% 4.35/0.93    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_209),
% 4.35/0.93    inference(forward_demodulation,[],[f6976,f569])).
% 4.35/0.93  fof(f569,plain,(
% 4.35/0.93    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 4.35/0.93    inference(backward_demodulation,[],[f129,f306])).
% 4.35/0.93  fof(f306,plain,(
% 4.35/0.93    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 4.35/0.93    inference(subsumption_resolution,[],[f297,f68])).
% 4.35/0.93  fof(f68,plain,(
% 4.35/0.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.35/0.93    inference(equality_resolution,[],[f50])).
% 4.35/0.93  fof(f50,plain,(
% 4.35/0.93    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.35/0.93    inference(cnf_transformation,[],[f41])).
% 4.35/0.93  fof(f297,plain,(
% 4.35/0.93    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X1)) )),
% 4.35/0.93    inference(superposition,[],[f129,f65])).
% 4.35/0.93  fof(f65,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f42])).
% 4.35/0.93  fof(f129,plain,(
% 4.35/0.93    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 4.35/0.93    inference(superposition,[],[f53,f67])).
% 4.35/0.93  fof(f67,plain,(
% 4.35/0.93    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.35/0.93    inference(cnf_transformation,[],[f7])).
% 4.35/0.93  fof(f7,axiom,(
% 4.35/0.93    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 4.35/0.93  fof(f6976,plain,(
% 4.35/0.93    k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_209),
% 4.35/0.93    inference(forward_demodulation,[],[f6975,f54])).
% 4.35/0.93  fof(f54,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f1])).
% 4.35/0.93  fof(f1,axiom,(
% 4.35/0.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.35/0.93  fof(f6975,plain,(
% 4.35/0.93    k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_209),
% 4.35/0.93    inference(forward_demodulation,[],[f6912,f590])).
% 4.35/0.93  fof(f590,plain,(
% 4.35/0.93    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.35/0.93    inference(forward_demodulation,[],[f583,f67])).
% 4.35/0.93  fof(f583,plain,(
% 4.35/0.93    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 4.35/0.93    inference(superposition,[],[f53,f569])).
% 4.35/0.93  fof(f6912,plain,(
% 4.35/0.93    k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | ~spl2_209),
% 4.35/0.93    inference(superposition,[],[f2231,f6797])).
% 4.35/0.93  fof(f6797,plain,(
% 4.35/0.93    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_209),
% 4.35/0.93    inference(avatar_component_clause,[],[f6795])).
% 4.35/0.93  fof(f2231,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.35/0.93    inference(backward_demodulation,[],[f421,f814])).
% 4.35/0.93  fof(f814,plain,(
% 4.35/0.93    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k3_xboole_0(X7,k3_xboole_0(X7,X8))) )),
% 4.35/0.93    inference(subsumption_resolution,[],[f788,f66])).
% 4.35/0.93  fof(f788,plain,(
% 4.35/0.93    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k3_xboole_0(X7,k3_xboole_0(X7,X8)) | ~r1_tarski(k4_xboole_0(X7,X8),X7)) )),
% 4.35/0.93    inference(superposition,[],[f415,f53])).
% 4.35/0.93  fof(f415,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_tarski(X1,X0)) )),
% 4.35/0.93    inference(superposition,[],[f131,f115])).
% 4.35/0.93  fof(f115,plain,(
% 4.35/0.93    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 4.35/0.93    inference(superposition,[],[f52,f54])).
% 4.35/0.93  fof(f131,plain,(
% 4.35/0.93    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 4.35/0.93    inference(superposition,[],[f53,f53])).
% 4.35/0.93  fof(f421,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.35/0.93    inference(superposition,[],[f53,f131])).
% 4.35/0.93  fof(f5031,plain,(
% 4.35/0.93    spl2_146 | ~spl2_2 | ~spl2_3 | ~spl2_10),
% 4.35/0.93    inference(avatar_split_clause,[],[f5026,f157,f81,f75,f5028])).
% 4.35/0.93  fof(f75,plain,(
% 4.35/0.93    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 4.35/0.93  fof(f157,plain,(
% 4.35/0.93    spl2_10 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 4.35/0.93  fof(f5026,plain,(
% 4.35/0.93    r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_10)),
% 4.35/0.93    inference(subsumption_resolution,[],[f5025,f158])).
% 4.35/0.93  fof(f158,plain,(
% 4.35/0.93    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_10),
% 4.35/0.93    inference(avatar_component_clause,[],[f157])).
% 4.35/0.93  fof(f5025,plain,(
% 4.35/0.93    r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 4.35/0.93    inference(subsumption_resolution,[],[f5008,f83])).
% 4.35/0.93  fof(f5008,plain,(
% 4.35/0.93    r1_tarski(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 4.35/0.93    inference(superposition,[],[f567,f76])).
% 4.35/0.93  fof(f76,plain,(
% 4.35/0.93    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 4.35/0.93    inference(avatar_component_clause,[],[f75])).
% 4.35/0.93  fof(f567,plain,(
% 4.35/0.93    ( ! [X10,X8,X9] : (r1_tarski(k7_subset_1(X9,X8,X10),k3_subset_1(X9,X10)) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | ~m1_subset_1(X8,k1_zfmisc_1(X9))) )),
% 4.35/0.93    inference(superposition,[],[f140,f223])).
% 4.35/0.93  fof(f140,plain,(
% 4.35/0.93    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) )),
% 4.35/0.93    inference(superposition,[],[f135,f54])).
% 4.35/0.93  fof(f135,plain,(
% 4.35/0.93    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X4,X5),X4)) )),
% 4.35/0.93    inference(superposition,[],[f66,f53])).
% 4.35/0.93  fof(f278,plain,(
% 4.35/0.93    spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_13),
% 4.35/0.93    inference(avatar_contradiction_clause,[],[f277])).
% 4.35/0.93  fof(f277,plain,(
% 4.35/0.93    $false | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_13)),
% 4.35/0.93    inference(subsumption_resolution,[],[f276,f88])).
% 4.35/0.93  fof(f276,plain,(
% 4.35/0.93    ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_3 | ~spl2_13)),
% 4.35/0.93    inference(subsumption_resolution,[],[f275,f83])).
% 4.35/0.93  fof(f275,plain,(
% 4.35/0.93    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_13)),
% 4.35/0.93    inference(subsumption_resolution,[],[f272,f77])).
% 4.35/0.93  fof(f77,plain,(
% 4.35/0.93    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 4.35/0.93    inference(avatar_component_clause,[],[f75])).
% 4.35/0.93  fof(f272,plain,(
% 4.35/0.93    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_13),
% 4.35/0.93    inference(superposition,[],[f55,f195])).
% 4.35/0.93  fof(f55,plain,(
% 4.35/0.93    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f25])).
% 4.35/0.93  fof(f25,plain,(
% 4.35/0.93    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.35/0.93    inference(ennf_transformation,[],[f16])).
% 4.35/0.93  fof(f16,axiom,(
% 4.35/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 4.35/0.93  fof(f203,plain,(
% 4.35/0.93    ~spl2_10 | spl2_11 | ~spl2_2),
% 4.35/0.93    inference(avatar_split_clause,[],[f200,f75,f161,f157])).
% 4.35/0.93  fof(f200,plain,(
% 4.35/0.93    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 4.35/0.93    inference(superposition,[],[f57,f76])).
% 4.35/0.93  fof(f57,plain,(
% 4.35/0.93    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.35/0.93    inference(cnf_transformation,[],[f27])).
% 4.35/0.93  fof(f27,plain,(
% 4.35/0.93    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.35/0.93    inference(ennf_transformation,[],[f10])).
% 4.35/0.93  fof(f10,axiom,(
% 4.35/0.93    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 4.35/0.93  fof(f197,plain,(
% 4.35/0.93    ~spl2_1 | spl2_13 | ~spl2_3 | ~spl2_4 | ~spl2_9),
% 4.35/0.93    inference(avatar_split_clause,[],[f190,f106,f86,f81,f193,f71])).
% 4.35/0.93  fof(f106,plain,(
% 4.35/0.93    spl2_9 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 4.35/0.93  fof(f190,plain,(
% 4.35/0.93    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_9)),
% 4.35/0.93    inference(subsumption_resolution,[],[f188,f88])).
% 4.35/0.93  fof(f188,plain,(
% 4.35/0.93    ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_9)),
% 4.35/0.93    inference(resolution,[],[f107,f83])).
% 4.35/0.93  fof(f107,plain,(
% 4.35/0.93    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl2_9),
% 4.35/0.93    inference(avatar_component_clause,[],[f106])).
% 4.35/0.93  fof(f176,plain,(
% 4.35/0.93    ~spl2_3 | ~spl2_4 | spl2_10),
% 4.35/0.93    inference(avatar_contradiction_clause,[],[f175])).
% 4.35/0.93  fof(f175,plain,(
% 4.35/0.93    $false | (~spl2_3 | ~spl2_4 | spl2_10)),
% 4.35/0.93    inference(subsumption_resolution,[],[f174,f88])).
% 4.35/0.93  fof(f174,plain,(
% 4.35/0.93    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_10)),
% 4.35/0.93    inference(subsumption_resolution,[],[f172,f83])).
% 4.35/0.93  fof(f172,plain,(
% 4.35/0.93    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_10),
% 4.35/0.93    inference(resolution,[],[f59,f159])).
% 4.35/0.93  fof(f159,plain,(
% 4.35/0.93    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_10),
% 4.35/0.93    inference(avatar_component_clause,[],[f157])).
% 4.35/0.93  fof(f59,plain,(
% 4.35/0.93    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f30])).
% 4.35/0.93  fof(f30,plain,(
% 4.35/0.93    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.35/0.93    inference(flattening,[],[f29])).
% 4.35/0.93  fof(f29,plain,(
% 4.35/0.93    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.35/0.93    inference(ennf_transformation,[],[f15])).
% 4.35/0.93  fof(f15,axiom,(
% 4.35/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 4.35/0.93  fof(f147,plain,(
% 4.35/0.93    ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_8),
% 4.35/0.93    inference(avatar_contradiction_clause,[],[f146])).
% 4.35/0.93  fof(f146,plain,(
% 4.35/0.93    $false | (~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_8)),
% 4.35/0.93    inference(subsumption_resolution,[],[f145,f88])).
% 4.35/0.93  fof(f145,plain,(
% 4.35/0.93    ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_5 | ~spl2_8)),
% 4.35/0.93    inference(subsumption_resolution,[],[f143,f93])).
% 4.35/0.93  fof(f143,plain,(
% 4.35/0.93    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_8)),
% 4.35/0.93    inference(resolution,[],[f104,f83])).
% 4.35/0.93  fof(f104,plain,(
% 4.35/0.93    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl2_8),
% 4.35/0.93    inference(avatar_component_clause,[],[f103])).
% 4.35/0.93  fof(f103,plain,(
% 4.35/0.93    spl2_8 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 4.35/0.93  fof(f114,plain,(
% 4.35/0.93    ~spl2_3 | ~spl2_4 | ~spl2_6),
% 4.35/0.93    inference(avatar_contradiction_clause,[],[f113])).
% 4.35/0.93  fof(f113,plain,(
% 4.35/0.93    $false | (~spl2_3 | ~spl2_4 | ~spl2_6)),
% 4.35/0.93    inference(subsumption_resolution,[],[f111,f88])).
% 4.35/0.93  fof(f111,plain,(
% 4.35/0.93    ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_6)),
% 4.35/0.93    inference(resolution,[],[f97,f83])).
% 4.35/0.93  fof(f97,plain,(
% 4.35/0.93    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl2_6),
% 4.35/0.93    inference(avatar_component_clause,[],[f96])).
% 4.35/0.93  fof(f96,plain,(
% 4.35/0.93    spl2_6 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 4.35/0.93    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 4.35/0.93  fof(f108,plain,(
% 4.35/0.93    spl2_8 | spl2_9),
% 4.35/0.93    inference(avatar_split_clause,[],[f60,f106,f103])).
% 4.35/0.93  fof(f60,plain,(
% 4.35/0.93    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f32])).
% 4.35/0.93  fof(f32,plain,(
% 4.35/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.35/0.93    inference(flattening,[],[f31])).
% 4.35/0.93  fof(f31,plain,(
% 4.35/0.93    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.35/0.93    inference(ennf_transformation,[],[f17])).
% 4.35/0.93  fof(f17,axiom,(
% 4.35/0.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 4.35/0.93  fof(f101,plain,(
% 4.35/0.93    spl2_6 | spl2_7),
% 4.35/0.93    inference(avatar_split_clause,[],[f61,f99,f96])).
% 4.35/0.93  fof(f61,plain,(
% 4.35/0.93    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 4.35/0.93    inference(cnf_transformation,[],[f32])).
% 4.35/0.93  fof(f94,plain,(
% 4.35/0.93    spl2_5),
% 4.35/0.93    inference(avatar_split_clause,[],[f43,f91])).
% 4.35/0.93  fof(f43,plain,(
% 4.35/0.93    v2_pre_topc(sK0)),
% 4.35/0.93    inference(cnf_transformation,[],[f39])).
% 4.35/0.93  fof(f39,plain,(
% 4.35/0.93    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 4.35/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 4.35/0.93  % (18099)Time limit reached!
% 4.35/0.93  % (18099)------------------------------
% 4.35/0.93  % (18099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (18099)Termination reason: Time limit
% 4.35/0.93  
% 4.35/0.93  % (18099)Memory used [KB]: 13688
% 4.35/0.93  % (18099)Time elapsed: 0.516 s
% 4.35/0.93  % (18099)------------------------------
% 4.35/0.93  % (18099)------------------------------
% 4.35/0.93  fof(f37,plain,(
% 4.35/0.93    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 4.35/0.93    introduced(choice_axiom,[])).
% 4.35/0.93  fof(f38,plain,(
% 4.35/0.93    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.35/0.93    introduced(choice_axiom,[])).
% 4.35/0.93  fof(f36,plain,(
% 4.35/0.93    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.35/0.93    inference(flattening,[],[f35])).
% 4.35/0.93  fof(f35,plain,(
% 4.35/0.93    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.35/0.93    inference(nnf_transformation,[],[f22])).
% 4.35/0.93  fof(f22,plain,(
% 4.35/0.93    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.35/0.93    inference(flattening,[],[f21])).
% 4.35/0.93  fof(f21,plain,(
% 4.35/0.93    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.35/0.93    inference(ennf_transformation,[],[f20])).
% 4.35/0.93  fof(f20,negated_conjecture,(
% 4.35/0.93    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 4.35/0.93    inference(negated_conjecture,[],[f19])).
% 4.35/0.93  fof(f19,conjecture,(
% 4.35/0.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 4.35/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 4.35/0.93  fof(f89,plain,(
% 4.35/0.93    spl2_4),
% 4.35/0.93    inference(avatar_split_clause,[],[f44,f86])).
% 4.35/0.93  fof(f44,plain,(
% 4.35/0.93    l1_pre_topc(sK0)),
% 4.35/0.93    inference(cnf_transformation,[],[f39])).
% 4.35/0.93  fof(f84,plain,(
% 4.35/0.93    spl2_3),
% 4.35/0.93    inference(avatar_split_clause,[],[f45,f81])).
% 4.35/0.93  fof(f45,plain,(
% 4.35/0.93    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.35/0.93    inference(cnf_transformation,[],[f39])).
% 4.35/0.93  fof(f79,plain,(
% 4.35/0.93    spl2_1 | spl2_2),
% 4.35/0.93    inference(avatar_split_clause,[],[f46,f75,f71])).
% 4.35/0.93  fof(f46,plain,(
% 4.35/0.93    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 4.35/0.93    inference(cnf_transformation,[],[f39])).
% 4.35/0.93  fof(f78,plain,(
% 4.35/0.93    ~spl2_1 | ~spl2_2),
% 4.35/0.93    inference(avatar_split_clause,[],[f47,f75,f71])).
% 4.35/0.93  fof(f47,plain,(
% 4.35/0.93    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 4.35/0.93    inference(cnf_transformation,[],[f39])).
% 4.35/0.93  % SZS output end Proof for theBenchmark
% 4.35/0.93  % (18107)Time limit reached!
% 4.35/0.93  % (18107)------------------------------
% 4.35/0.93  % (18107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (18114)------------------------------
% 4.35/0.93  % (18114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (18114)Termination reason: Refutation
% 4.35/0.93  
% 4.35/0.93  % (18114)Memory used [KB]: 10490
% 4.35/0.93  % (18114)Time elapsed: 0.498 s
% 4.35/0.93  % (18114)------------------------------
% 4.35/0.93  % (18114)------------------------------
% 4.35/0.94  % (18092)Success in time 0.569 s
%------------------------------------------------------------------------------
