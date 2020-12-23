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
% DateTime   : Thu Dec  3 13:12:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 197 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  343 ( 697 expanded)
%              Number of equality atoms :   74 ( 164 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f363,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f74,f79,f84,f89,f108,f136,f145,f341,f342,f343,f362])).

fof(f362,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f360,f83])).

fof(f83,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f360,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f359,f78])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f359,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_2
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f353,f72])).

fof(f72,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f353,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_16 ),
    inference(superposition,[],[f50,f338])).

fof(f338,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl2_16
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f343,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f342,plain,
    ( ~ spl2_10
    | spl2_16
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f333,f81,f76,f336,f133])).

fof(f133,plain,
    ( spl2_10
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f333,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f329,f83])).

fof(f329,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f315,f78])).

fof(f315,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | k2_pre_topc(X3,X2) = X2
      | ~ l1_pre_topc(X3)
      | ~ r1_tarski(k2_tops_1(X3,X2),X2) ) ),
    inference(subsumption_resolution,[],[f191,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f110,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f56,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f191,plain,(
    ! [X2,X3] :
      ( k2_pre_topc(X3,X2) = X2
      | ~ m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(u1_struct_0(X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ r1_tarski(k2_tops_1(X3,X2),X2) ) ),
    inference(superposition,[],[f150,f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f97,f181])).

fof(f181,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f179,f94])).

fof(f94,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f91,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f91,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k1_xboole_0,X2) ) ),
    inference(superposition,[],[f61,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f179,plain,(
    ! [X0] :
      ( k5_xboole_0(X0,k1_xboole_0) = X0
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f97,f62])).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f60,f58])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f150,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f54,f52])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f54,plain,(
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

fof(f341,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f340,f81,f76,f66,f133])).

fof(f66,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f340,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f146,f83])).

fof(f146,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f51,f78])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f145,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f140,f86,f81,f76,f142])).

fof(f142,plain,
    ( spl2_11
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f86,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f140,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f139,f88])).

fof(f88,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f139,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f137,f83])).

fof(f137,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f53,f78])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f136,plain,
    ( spl2_10
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f115,f103,f133])).

fof(f103,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f115,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_6 ),
    inference(superposition,[],[f61,f105])).

fof(f105,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f108,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f107,f76,f70,f103])).

fof(f107,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f100,f78])).

fof(f100,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f71,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f71,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f89,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
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

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

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

fof(f84,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f41,f81])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f42,f76])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f43,f70,f66])).

fof(f43,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f44,f70,f66])).

fof(f44,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (18911)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (18913)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (18919)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (18928)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.51  % (18914)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (18912)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (18909)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (18909)Refutation not found, incomplete strategy% (18909)------------------------------
% 0.21/0.52  % (18909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18909)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18909)Memory used [KB]: 1663
% 0.21/0.52  % (18909)Time elapsed: 0.103 s
% 0.21/0.52  % (18909)------------------------------
% 0.21/0.52  % (18909)------------------------------
% 0.21/0.52  % (18916)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (18937)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (18937)Refutation not found, incomplete strategy% (18937)------------------------------
% 0.21/0.52  % (18937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18937)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18937)Memory used [KB]: 10746
% 0.21/0.52  % (18937)Time elapsed: 0.119 s
% 0.21/0.52  % (18937)------------------------------
% 0.21/0.52  % (18937)------------------------------
% 0.21/0.52  % (18930)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (18920)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (18924)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (18932)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (18923)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (18913)Refutation not found, incomplete strategy% (18913)------------------------------
% 0.21/0.53  % (18913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18939)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (18913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18913)Memory used [KB]: 1791
% 0.21/0.53  % (18913)Time elapsed: 0.105 s
% 0.21/0.53  % (18913)------------------------------
% 0.21/0.53  % (18913)------------------------------
% 0.21/0.53  % (18939)Refutation not found, incomplete strategy% (18939)------------------------------
% 0.21/0.53  % (18939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18939)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18939)Memory used [KB]: 1663
% 0.21/0.53  % (18939)Time elapsed: 0.001 s
% 0.21/0.53  % (18939)------------------------------
% 0.21/0.53  % (18939)------------------------------
% 0.21/0.53  % (18934)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (18908)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (18910)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (18936)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (18917)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (18922)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (18931)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (18915)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (18935)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (18929)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (18927)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (18935)Refutation not found, incomplete strategy% (18935)------------------------------
% 0.21/0.54  % (18935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18935)Memory used [KB]: 6268
% 0.21/0.54  % (18935)Time elapsed: 0.137 s
% 0.21/0.54  % (18935)------------------------------
% 0.21/0.54  % (18935)------------------------------
% 0.21/0.54  % (18933)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (18920)Refutation not found, incomplete strategy% (18920)------------------------------
% 0.21/0.55  % (18920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18930)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (18918)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (18920)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18920)Memory used [KB]: 10746
% 0.21/0.55  % (18920)Time elapsed: 0.141 s
% 0.21/0.55  % (18920)------------------------------
% 0.21/0.55  % (18920)------------------------------
% 0.21/0.55  % (18925)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.53/0.55  % (18926)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.53/0.55  % (18925)Refutation not found, incomplete strategy% (18925)------------------------------
% 1.53/0.55  % (18925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (18925)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.55  
% 1.53/0.55  % (18925)Memory used [KB]: 10618
% 1.53/0.55  % (18925)Time elapsed: 0.151 s
% 1.53/0.55  % (18925)------------------------------
% 1.53/0.55  % (18925)------------------------------
% 1.53/0.55  % SZS output start Proof for theBenchmark
% 1.53/0.55  fof(f363,plain,(
% 1.53/0.55    $false),
% 1.53/0.55    inference(avatar_sat_refutation,[],[f73,f74,f79,f84,f89,f108,f136,f145,f341,f342,f343,f362])).
% 1.53/0.55  fof(f362,plain,(
% 1.53/0.55    spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_16),
% 1.53/0.55    inference(avatar_contradiction_clause,[],[f361])).
% 1.53/0.55  fof(f361,plain,(
% 1.53/0.55    $false | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_16)),
% 1.53/0.55    inference(subsumption_resolution,[],[f360,f83])).
% 1.53/0.55  fof(f83,plain,(
% 1.53/0.55    l1_pre_topc(sK0) | ~spl2_4),
% 1.53/0.55    inference(avatar_component_clause,[],[f81])).
% 1.53/0.55  fof(f81,plain,(
% 1.53/0.55    spl2_4 <=> l1_pre_topc(sK0)),
% 1.53/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.53/0.55  fof(f360,plain,(
% 1.53/0.55    ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_3 | ~spl2_16)),
% 1.53/0.55    inference(subsumption_resolution,[],[f359,f78])).
% 1.53/0.55  fof(f78,plain,(
% 1.53/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.53/0.55    inference(avatar_component_clause,[],[f76])).
% 1.53/0.55  fof(f76,plain,(
% 1.53/0.55    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.53/0.55  fof(f359,plain,(
% 1.53/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_2 | ~spl2_16)),
% 1.53/0.55    inference(subsumption_resolution,[],[f353,f72])).
% 1.53/0.55  fof(f72,plain,(
% 1.53/0.55    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 1.53/0.55    inference(avatar_component_clause,[],[f70])).
% 1.53/0.55  fof(f70,plain,(
% 1.53/0.55    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.53/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.53/0.55  fof(f353,plain,(
% 1.53/0.55    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_16),
% 1.53/0.55    inference(superposition,[],[f50,f338])).
% 1.53/0.55  fof(f338,plain,(
% 1.53/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_16),
% 1.53/0.55    inference(avatar_component_clause,[],[f336])).
% 1.53/0.55  fof(f336,plain,(
% 1.53/0.55    spl2_16 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.53/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.53/0.55  fof(f50,plain,(
% 1.53/0.55    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f22])).
% 1.53/0.55  fof(f22,plain,(
% 1.53/0.55    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.55    inference(ennf_transformation,[],[f13])).
% 1.53/0.55  fof(f13,axiom,(
% 1.53/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.53/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.53/0.55  fof(f343,plain,(
% 1.53/0.55    sK1 != k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0) | ~v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 1.53/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.55  fof(f342,plain,(
% 1.53/0.55    ~spl2_10 | spl2_16 | ~spl2_3 | ~spl2_4),
% 1.53/0.55    inference(avatar_split_clause,[],[f333,f81,f76,f336,f133])).
% 1.53/0.55  fof(f133,plain,(
% 1.53/0.55    spl2_10 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 1.53/0.55    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.53/0.55  fof(f333,plain,(
% 1.53/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 1.53/0.55    inference(subsumption_resolution,[],[f329,f83])).
% 1.53/0.55  fof(f329,plain,(
% 1.53/0.55    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_3),
% 1.53/0.55    inference(resolution,[],[f315,f78])).
% 1.53/0.55  fof(f315,plain,(
% 1.53/0.55    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | k2_pre_topc(X3,X2) = X2 | ~l1_pre_topc(X3) | ~r1_tarski(k2_tops_1(X3,X2),X2)) )),
% 1.53/0.55    inference(subsumption_resolution,[],[f191,f185])).
% 1.53/0.55  fof(f185,plain,(
% 1.53/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,k1_zfmisc_1(X2)) | ~r1_tarski(X0,X1)) )),
% 1.53/0.55    inference(superposition,[],[f110,f49])).
% 1.53/0.55  fof(f49,plain,(
% 1.53/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.53/0.55    inference(cnf_transformation,[],[f21])).
% 1.53/0.55  fof(f21,plain,(
% 1.53/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/0.55    inference(ennf_transformation,[],[f5])).
% 1.53/0.55  fof(f5,axiom,(
% 1.53/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.53/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.53/0.55  fof(f110,plain,(
% 1.53/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.53/0.55    inference(duplicate_literal_removal,[],[f109])).
% 1.53/0.55  fof(f109,plain,(
% 1.53/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.53/0.55    inference(superposition,[],[f56,f55])).
% 1.53/0.55  fof(f55,plain,(
% 1.53/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.53/0.55    inference(cnf_transformation,[],[f30])).
% 1.53/0.55  fof(f30,plain,(
% 1.53/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.53/0.55    inference(ennf_transformation,[],[f11])).
% 1.53/0.56  fof(f11,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.53/0.56  fof(f56,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f31])).
% 1.53/0.56  fof(f31,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f8])).
% 1.53/0.56  fof(f8,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.53/0.56  fof(f191,plain,(
% 1.53/0.56    ( ! [X2,X3] : (k2_pre_topc(X3,X2) = X2 | ~m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(u1_struct_0(X3))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~r1_tarski(k2_tops_1(X3,X2),X2)) )),
% 1.53/0.56    inference(superposition,[],[f150,f188])).
% 1.53/0.56  fof(f188,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = X1 | ~r1_tarski(X0,X1)) )),
% 1.53/0.56    inference(backward_demodulation,[],[f97,f181])).
% 1.53/0.56  fof(f181,plain,(
% 1.53/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.56    inference(subsumption_resolution,[],[f179,f94])).
% 1.53/0.56  fof(f94,plain,(
% 1.53/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.56    inference(resolution,[],[f91,f63])).
% 1.53/0.56  fof(f63,plain,(
% 1.53/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.53/0.56    inference(equality_resolution,[],[f47])).
% 1.53/0.56  fof(f47,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.53/0.56    inference(cnf_transformation,[],[f38])).
% 1.53/0.56  fof(f38,plain,(
% 1.53/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.56    inference(flattening,[],[f37])).
% 1.53/0.56  fof(f37,plain,(
% 1.53/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.53/0.56    inference(nnf_transformation,[],[f1])).
% 1.53/0.56  fof(f1,axiom,(
% 1.53/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.53/0.56  fof(f91,plain,(
% 1.53/0.56    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k1_xboole_0,X2)) )),
% 1.53/0.56    inference(superposition,[],[f61,f58])).
% 1.53/0.56  fof(f58,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f39])).
% 1.53/0.56  fof(f39,plain,(
% 1.53/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.53/0.56    inference(nnf_transformation,[],[f2])).
% 1.53/0.56  fof(f2,axiom,(
% 1.53/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.53/0.56  fof(f61,plain,(
% 1.53/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f6])).
% 1.53/0.56  fof(f6,axiom,(
% 1.53/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.53/0.56  fof(f179,plain,(
% 1.53/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0 | ~r1_tarski(k1_xboole_0,X0)) )),
% 1.53/0.56    inference(superposition,[],[f97,f62])).
% 1.53/0.56  fof(f62,plain,(
% 1.53/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.56    inference(cnf_transformation,[],[f4])).
% 1.53/0.56  fof(f4,axiom,(
% 1.53/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.53/0.56  fof(f97,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 1.53/0.56    inference(superposition,[],[f60,f58])).
% 1.53/0.56  fof(f60,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f7])).
% 1.53/0.56  fof(f7,axiom,(
% 1.53/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.53/0.56  fof(f150,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(duplicate_literal_removal,[],[f149])).
% 1.53/0.56  fof(f149,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(superposition,[],[f54,f52])).
% 1.53/0.56  fof(f52,plain,(
% 1.53/0.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f25])).
% 1.53/0.56  fof(f25,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f14])).
% 1.53/0.56  fof(f14,axiom,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.53/0.56  fof(f54,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f29])).
% 1.53/0.56  fof(f29,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.56    inference(flattening,[],[f28])).
% 1.53/0.56  fof(f28,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.53/0.56    inference(ennf_transformation,[],[f9])).
% 1.53/0.56  fof(f9,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.53/0.56  fof(f341,plain,(
% 1.53/0.56    spl2_10 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 1.53/0.56    inference(avatar_split_clause,[],[f340,f81,f76,f66,f133])).
% 1.53/0.56  fof(f66,plain,(
% 1.53/0.56    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.53/0.56  fof(f340,plain,(
% 1.53/0.56    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 1.53/0.56    inference(subsumption_resolution,[],[f146,f83])).
% 1.53/0.56  fof(f146,plain,(
% 1.53/0.56    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 1.53/0.56    inference(resolution,[],[f51,f78])).
% 1.53/0.56  fof(f51,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f24])).
% 1.53/0.56  fof(f24,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f23])).
% 1.53/0.56  fof(f23,plain,(
% 1.53/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.56    inference(ennf_transformation,[],[f15])).
% 1.53/0.56  fof(f15,axiom,(
% 1.53/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 1.53/0.56  fof(f145,plain,(
% 1.53/0.56    spl2_11 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 1.53/0.56    inference(avatar_split_clause,[],[f140,f86,f81,f76,f142])).
% 1.53/0.56  fof(f142,plain,(
% 1.53/0.56    spl2_11 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.53/0.56  fof(f86,plain,(
% 1.53/0.56    spl2_5 <=> v2_pre_topc(sK0)),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.53/0.56  fof(f140,plain,(
% 1.53/0.56    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 1.53/0.56    inference(subsumption_resolution,[],[f139,f88])).
% 1.53/0.56  fof(f88,plain,(
% 1.53/0.56    v2_pre_topc(sK0) | ~spl2_5),
% 1.53/0.56    inference(avatar_component_clause,[],[f86])).
% 1.53/0.56  fof(f139,plain,(
% 1.53/0.56    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl2_3 | ~spl2_4)),
% 1.53/0.56    inference(subsumption_resolution,[],[f137,f83])).
% 1.53/0.56  fof(f137,plain,(
% 1.53/0.56    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 1.53/0.56    inference(resolution,[],[f53,f78])).
% 1.53/0.56  fof(f53,plain,(
% 1.53/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.53/0.56    inference(cnf_transformation,[],[f27])).
% 1.53/0.56  fof(f27,plain,(
% 1.53/0.56    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f26])).
% 1.53/0.56  fof(f26,plain,(
% 1.53/0.56    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f12])).
% 1.53/0.56  fof(f12,axiom,(
% 1.53/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.53/0.56  fof(f136,plain,(
% 1.53/0.56    spl2_10 | ~spl2_6),
% 1.53/0.56    inference(avatar_split_clause,[],[f115,f103,f133])).
% 1.53/0.56  fof(f103,plain,(
% 1.53/0.56    spl2_6 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.53/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.53/0.56  fof(f115,plain,(
% 1.53/0.56    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_6),
% 1.53/0.56    inference(superposition,[],[f61,f105])).
% 1.53/0.56  fof(f105,plain,(
% 1.53/0.56    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 1.53/0.56    inference(avatar_component_clause,[],[f103])).
% 1.53/0.56  fof(f108,plain,(
% 1.53/0.56    spl2_6 | ~spl2_2 | ~spl2_3),
% 1.53/0.56    inference(avatar_split_clause,[],[f107,f76,f70,f103])).
% 1.53/0.56  fof(f107,plain,(
% 1.53/0.56    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 1.53/0.56    inference(subsumption_resolution,[],[f100,f78])).
% 1.53/0.56  fof(f100,plain,(
% 1.53/0.56    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.53/0.56    inference(superposition,[],[f71,f45])).
% 1.53/0.56  fof(f45,plain,(
% 1.53/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.53/0.56    inference(cnf_transformation,[],[f20])).
% 1.53/0.56  fof(f20,plain,(
% 1.53/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f10])).
% 1.53/0.56  fof(f10,axiom,(
% 1.53/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.53/0.56  fof(f71,plain,(
% 1.53/0.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 1.53/0.56    inference(avatar_component_clause,[],[f70])).
% 1.53/0.56  fof(f89,plain,(
% 1.53/0.56    spl2_5),
% 1.53/0.56    inference(avatar_split_clause,[],[f40,f86])).
% 1.53/0.56  fof(f40,plain,(
% 1.53/0.56    v2_pre_topc(sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f36])).
% 1.53/0.56  fof(f36,plain,(
% 1.53/0.56    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.53/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 1.53/0.56  fof(f34,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f35,plain,(
% 1.53/0.56    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.53/0.56    introduced(choice_axiom,[])).
% 1.53/0.56  fof(f33,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f32])).
% 1.53/0.56  fof(f32,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.53/0.56    inference(nnf_transformation,[],[f19])).
% 1.53/0.56  fof(f19,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.53/0.56    inference(flattening,[],[f18])).
% 1.53/0.56  fof(f18,plain,(
% 1.53/0.56    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.53/0.56    inference(ennf_transformation,[],[f17])).
% 1.53/0.56  fof(f17,negated_conjecture,(
% 1.53/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.53/0.56    inference(negated_conjecture,[],[f16])).
% 1.53/0.56  fof(f16,conjecture,(
% 1.53/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 1.53/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 1.53/0.56  fof(f84,plain,(
% 1.53/0.56    spl2_4),
% 1.53/0.56    inference(avatar_split_clause,[],[f41,f81])).
% 1.53/0.56  fof(f41,plain,(
% 1.53/0.56    l1_pre_topc(sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f36])).
% 1.53/0.56  fof(f79,plain,(
% 1.53/0.56    spl2_3),
% 1.53/0.56    inference(avatar_split_clause,[],[f42,f76])).
% 1.53/0.56  fof(f42,plain,(
% 1.53/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.53/0.56    inference(cnf_transformation,[],[f36])).
% 1.53/0.56  fof(f74,plain,(
% 1.53/0.56    spl2_1 | spl2_2),
% 1.53/0.56    inference(avatar_split_clause,[],[f43,f70,f66])).
% 1.53/0.56  fof(f43,plain,(
% 1.53/0.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f36])).
% 1.53/0.56  fof(f73,plain,(
% 1.53/0.56    ~spl2_1 | ~spl2_2),
% 1.53/0.56    inference(avatar_split_clause,[],[f44,f70,f66])).
% 1.53/0.56  fof(f44,plain,(
% 1.53/0.56    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 1.53/0.56    inference(cnf_transformation,[],[f36])).
% 1.53/0.56  % SZS output end Proof for theBenchmark
% 1.53/0.56  % (18930)------------------------------
% 1.53/0.56  % (18930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (18930)Termination reason: Refutation
% 1.53/0.56  
% 1.53/0.56  % (18930)Memory used [KB]: 6396
% 1.53/0.56  % (18930)Time elapsed: 0.130 s
% 1.53/0.56  % (18930)------------------------------
% 1.53/0.56  % (18930)------------------------------
% 1.53/0.56  % (18905)Success in time 0.196 s
%------------------------------------------------------------------------------
