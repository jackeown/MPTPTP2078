%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:20 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 284 expanded)
%              Number of leaves         :   33 ( 114 expanded)
%              Depth                    :   10
%              Number of atoms          :  296 ( 566 expanded)
%              Number of equality atoms :   78 ( 194 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2053,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f198,f242,f295,f437,f442,f843,f895,f942,f1785,f1787,f1823,f1874,f2048,f2050,f2052])).

fof(f2052,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2050,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_26
    | ~ spl3_3
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f2049,f2045,f75,f903,f65,f939])).

fof(f939,plain,
    ( spl3_31
  <=> v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f65,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f903,plain,
    ( spl3_26
  <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f75,plain,
    ( spl3_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f2045,plain,
    ( spl3_58
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f2049,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_58 ),
    inference(superposition,[],[f35,f2047])).

fof(f2047,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f2045])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f2048,plain,
    ( spl3_58
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f2042,f840,f2045])).

fof(f840,plain,
    ( spl3_23
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f2042,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl3_23 ),
    inference(superposition,[],[f1575,f842])).

fof(f842,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f840])).

fof(f1575,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(superposition,[],[f1574,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1574,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(forward_demodulation,[],[f102,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f40,f39,f51,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f102,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(resolution,[],[f54,f84])).

fof(f84,plain,(
    ! [X0,X1] : m1_subset_1(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1874,plain,
    ( spl3_26
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f1837,f840,f903])).

fof(f1837,plain,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_23 ),
    inference(superposition,[],[f89,f842])).

fof(f89,plain,(
    ! [X0,X1] : m1_subset_1(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f85,f44])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))),X0) ),
    inference(superposition,[],[f52,f38])).

fof(f1823,plain,
    ( spl3_23
    | spl3_22 ),
    inference(avatar_split_clause,[],[f1822,f836,f840])).

fof(f836,plain,
    ( spl3_22
  <=> r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1822,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | spl3_22 ),
    inference(forward_demodulation,[],[f1818,f38])).

fof(f1818,plain,
    ( sK1 = k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))
    | spl3_22 ),
    inference(resolution,[],[f838,f153])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X1 ) ),
    inference(factoring,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f838,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f836])).

fof(f1787,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1786,f80,f106])).

fof(f106,plain,
    ( spl3_5
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f80,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1786,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f1783,f38])).

fof(f1783,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))
    | ~ spl3_4 ),
    inference(resolution,[],[f82,f54])).

fof(f82,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f1785,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1780,f80,f65,f178])).

fof(f178,plain,
    ( spl3_8
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f1780,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_4 ),
    inference(resolution,[],[f82,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f942,plain,
    ( ~ spl3_31
    | spl3_18
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f924,f892,f425,f939])).

fof(f425,plain,
    ( spl3_18
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f892,plain,
    ( spl3_24
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f924,plain,
    ( ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | spl3_18
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f427,f894])).

fof(f894,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f892])).

fof(f427,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f425])).

fof(f895,plain,
    ( spl3_24
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f859,f840,f106,f892])).

fof(f859,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f108,f842])).

fof(f108,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f843,plain,
    ( ~ spl3_22
    | spl3_23
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f834,f80,f840,f836])).

fof(f834,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f833,f38])).

fof(f833,plain,
    ( sK1 = k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))
    | ~ r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1)
    | ~ spl3_4 ),
    inference(duplicate_literal_removal,[],[f823])).

fof(f823,plain,
    ( sK1 = k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))
    | ~ r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1)
    | ~ r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1)
    | sK1 = k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f213,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f213,plain,
    ( ! [X16] :
        ( r2_hidden(sK2(X16,sK1,sK1),u1_struct_0(sK0))
        | sK1 = k1_setfam_1(k2_tarski(X16,sK1)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f153,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f43,f82])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f442,plain,
    ( spl3_21
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f412,f239,f439])).

fof(f439,plain,
    ( spl3_21
  <=> k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f239,plain,
    ( spl3_10
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f412,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_10 ),
    inference(resolution,[],[f241,f54])).

fof(f241,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f239])).

fof(f437,plain,
    ( spl3_20
    | ~ spl3_18
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f411,f239,f65,f425,f434])).

fof(f434,plain,
    ( spl3_20
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f411,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl3_10 ),
    inference(resolution,[],[f241,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
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

fof(f295,plain,
    ( spl3_15
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f286,f106,f292])).

fof(f292,plain,
    ( spl3_15
  <=> k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f286,plain,
    ( k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl3_5 ),
    inference(superposition,[],[f129,f108])).

fof(f129,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))))) ),
    inference(superposition,[],[f53,f38])).

fof(f242,plain,
    ( spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f236,f106,f239])).

fof(f236,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f89,f108])).

fof(f198,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f189,f80,f65,f195])).

fof(f195,plain,
    ( spl3_9
  <=> k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f189,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ spl3_4 ),
    inference(resolution,[],[f33,f82])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_1)).

fof(f83,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f80])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tops_1)).

fof(f78,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f70,plain,
    ( spl3_2
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f30,plain,(
    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (15238)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (15238)Refutation not found, incomplete strategy% (15238)------------------------------
% 0.21/0.55  % (15238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15238)Memory used [KB]: 10746
% 0.21/0.55  % (15238)Time elapsed: 0.124 s
% 0.21/0.55  % (15238)------------------------------
% 0.21/0.55  % (15238)------------------------------
% 0.21/0.55  % (15262)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (15246)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (15240)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (15240)Refutation not found, incomplete strategy% (15240)------------------------------
% 0.21/0.57  % (15240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15245)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (15246)Refutation not found, incomplete strategy% (15246)------------------------------
% 0.21/0.57  % (15246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (15246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (15246)Memory used [KB]: 10618
% 0.21/0.57  % (15246)Time elapsed: 0.129 s
% 0.21/0.57  % (15246)------------------------------
% 0.21/0.57  % (15246)------------------------------
% 0.21/0.57  % (15256)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (15240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (15240)Memory used [KB]: 6268
% 0.21/0.57  % (15240)Time elapsed: 0.127 s
% 0.21/0.57  % (15240)------------------------------
% 0.21/0.57  % (15240)------------------------------
% 0.21/0.57  % (15239)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (15242)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (15241)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (15248)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.58  % (15256)Refutation not found, incomplete strategy% (15256)------------------------------
% 1.51/0.58  % (15256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (15237)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.58  % (15244)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.51/0.59  % (15256)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.59  
% 1.51/0.59  % (15256)Memory used [KB]: 10746
% 1.51/0.59  % (15256)Time elapsed: 0.148 s
% 1.51/0.59  % (15256)------------------------------
% 1.51/0.59  % (15256)------------------------------
% 1.51/0.59  % (15251)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.59  % (15245)Refutation not found, incomplete strategy% (15245)------------------------------
% 1.51/0.59  % (15245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (15245)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.59  
% 1.51/0.59  % (15245)Memory used [KB]: 10746
% 1.51/0.59  % (15245)Time elapsed: 0.159 s
% 1.51/0.59  % (15245)------------------------------
% 1.51/0.59  % (15245)------------------------------
% 1.51/0.59  % (15259)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.51/0.60  % (15263)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.84/0.60  % (15261)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.84/0.60  % (15236)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.84/0.60  % (15236)Refutation not found, incomplete strategy% (15236)------------------------------
% 1.84/0.60  % (15236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (15236)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.60  
% 1.84/0.60  % (15236)Memory used [KB]: 1791
% 1.84/0.60  % (15236)Time elapsed: 0.170 s
% 1.84/0.60  % (15236)------------------------------
% 1.84/0.60  % (15236)------------------------------
% 1.84/0.60  % (15260)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.84/0.60  % (15265)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.84/0.60  % (15244)Refutation not found, incomplete strategy% (15244)------------------------------
% 1.84/0.60  % (15244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (15244)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.60  
% 1.84/0.60  % (15244)Memory used [KB]: 10746
% 1.84/0.60  % (15244)Time elapsed: 0.170 s
% 1.84/0.60  % (15244)------------------------------
% 1.84/0.60  % (15244)------------------------------
% 1.84/0.61  % (15252)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.84/0.61  % (15257)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.84/0.61  % (15264)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.84/0.61  % (15258)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.84/0.61  % (15253)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.84/0.61  % (15258)Refutation not found, incomplete strategy% (15258)------------------------------
% 1.84/0.61  % (15258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (15258)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (15258)Memory used [KB]: 10746
% 1.84/0.61  % (15258)Time elapsed: 0.182 s
% 1.84/0.61  % (15258)------------------------------
% 1.84/0.61  % (15258)------------------------------
% 1.84/0.61  % (15249)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.84/0.61  % (15247)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.84/0.61  % (15253)Refutation not found, incomplete strategy% (15253)------------------------------
% 1.84/0.61  % (15253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (15253)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (15253)Memory used [KB]: 10618
% 1.84/0.61  % (15253)Time elapsed: 0.150 s
% 1.84/0.61  % (15253)------------------------------
% 1.84/0.61  % (15253)------------------------------
% 1.84/0.62  % (15247)Refutation not found, incomplete strategy% (15247)------------------------------
% 1.84/0.62  % (15247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.62  % (15255)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.84/0.62  % (15243)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.84/0.62  % (15250)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.84/0.63  % (15254)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.84/0.63  % (15247)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.63  
% 1.84/0.63  % (15247)Memory used [KB]: 10618
% 1.84/0.63  % (15247)Time elapsed: 0.184 s
% 1.84/0.63  % (15247)------------------------------
% 1.84/0.63  % (15247)------------------------------
% 2.18/0.68  % (15291)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.18/0.69  % (15290)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.18/0.69  % (15290)Refutation not found, incomplete strategy% (15290)------------------------------
% 2.18/0.69  % (15290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.69  % (15290)Termination reason: Refutation not found, incomplete strategy
% 2.18/0.69  
% 2.18/0.69  % (15290)Memory used [KB]: 6268
% 2.18/0.69  % (15290)Time elapsed: 0.098 s
% 2.18/0.69  % (15290)------------------------------
% 2.18/0.69  % (15290)------------------------------
% 2.18/0.70  % (15293)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.18/0.70  % (15292)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.18/0.71  % (15294)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.18/0.73  % (15295)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.18/0.74  % (15297)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.18/0.74  % (15298)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.18/0.75  % (15252)Refutation found. Thanks to Tanya!
% 2.18/0.75  % SZS status Theorem for theBenchmark
% 2.18/0.75  % SZS output start Proof for theBenchmark
% 2.18/0.75  fof(f2053,plain,(
% 2.18/0.75    $false),
% 2.18/0.75    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f198,f242,f295,f437,f442,f843,f895,f942,f1785,f1787,f1823,f1874,f2048,f2050,f2052])).
% 2.18/0.75  fof(f2052,plain,(
% 2.18/0.75    k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | sK1 != k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | k1_tops_1(sK0,sK1) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 2.18/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.18/0.75  fof(f2050,plain,(
% 2.18/0.75    spl3_31 | ~spl3_1 | ~spl3_26 | ~spl3_3 | ~spl3_58),
% 2.18/0.75    inference(avatar_split_clause,[],[f2049,f2045,f75,f903,f65,f939])).
% 2.18/0.75  fof(f939,plain,(
% 2.18/0.75    spl3_31 <=> v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.18/0.75  fof(f65,plain,(
% 2.18/0.75    spl3_1 <=> l1_pre_topc(sK0)),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.18/0.75  fof(f903,plain,(
% 2.18/0.75    spl3_26 <=> m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.18/0.75  fof(f75,plain,(
% 2.18/0.75    spl3_3 <=> v3_pre_topc(sK1,sK0)),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.18/0.75  fof(f2045,plain,(
% 2.18/0.75    spl3_58 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 2.18/0.75  fof(f2049,plain,(
% 2.18/0.75    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~spl3_58),
% 2.18/0.75    inference(superposition,[],[f35,f2047])).
% 2.18/0.75  fof(f2047,plain,(
% 2.18/0.75    sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | ~spl3_58),
% 2.18/0.75    inference(avatar_component_clause,[],[f2045])).
% 2.18/0.75  fof(f35,plain,(
% 2.18/0.75    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 2.18/0.75    inference(cnf_transformation,[],[f24])).
% 2.18/0.75  fof(f24,plain,(
% 2.18/0.75    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.75    inference(ennf_transformation,[],[f12])).
% 2.18/0.75  fof(f12,axiom,(
% 2.18/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 2.18/0.75  fof(f2048,plain,(
% 2.18/0.75    spl3_58 | ~spl3_23),
% 2.18/0.75    inference(avatar_split_clause,[],[f2042,f840,f2045])).
% 2.18/0.75  fof(f840,plain,(
% 2.18/0.75    spl3_23 <=> sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.18/0.75  fof(f2042,plain,(
% 2.18/0.75    sK1 = k3_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1)) | ~spl3_23),
% 2.18/0.75    inference(superposition,[],[f1575,f842])).
% 2.18/0.75  fof(f842,plain,(
% 2.18/0.75    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl3_23),
% 2.18/0.75    inference(avatar_component_clause,[],[f840])).
% 2.18/0.75  fof(f1575,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 2.18/0.75    inference(superposition,[],[f1574,f38])).
% 2.18/0.75  fof(f38,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.18/0.75    inference(cnf_transformation,[],[f5])).
% 2.18/0.75  fof(f5,axiom,(
% 2.18/0.75    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.18/0.75  fof(f1574,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 2.18/0.75    inference(forward_demodulation,[],[f102,f53])).
% 2.18/0.75  fof(f53,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 2.18/0.75    inference(definition_unfolding,[],[f40,f39,f51,f51])).
% 2.18/0.75  fof(f51,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.18/0.75    inference(definition_unfolding,[],[f41,f39])).
% 2.18/0.75  fof(f41,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.75    inference(cnf_transformation,[],[f2])).
% 2.18/0.75  fof(f2,axiom,(
% 2.18/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.18/0.75  fof(f39,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.18/0.75    inference(cnf_transformation,[],[f8])).
% 2.18/0.75  fof(f8,axiom,(
% 2.18/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.18/0.75  fof(f40,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.18/0.75    inference(cnf_transformation,[],[f4])).
% 2.18/0.75  fof(f4,axiom,(
% 2.18/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.18/0.75  fof(f102,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) = k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 2.18/0.75    inference(resolution,[],[f54,f84])).
% 2.18/0.75  fof(f84,plain,(
% 2.18/0.75    ( ! [X0,X1] : (m1_subset_1(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_zfmisc_1(X0))) )),
% 2.18/0.75    inference(resolution,[],[f52,f44])).
% 2.18/0.75  fof(f44,plain,(
% 2.18/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.18/0.75    inference(cnf_transformation,[],[f27])).
% 2.18/0.75  fof(f27,plain,(
% 2.18/0.75    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.18/0.75    inference(ennf_transformation,[],[f16])).
% 2.18/0.75  fof(f16,plain,(
% 2.18/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.18/0.75    inference(unused_predicate_definition_removal,[],[f9])).
% 2.18/0.75  fof(f9,axiom,(
% 2.18/0.75    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.18/0.75  fof(f52,plain,(
% 2.18/0.75    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.18/0.75    inference(definition_unfolding,[],[f37,f51])).
% 2.18/0.75  fof(f37,plain,(
% 2.18/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.18/0.75    inference(cnf_transformation,[],[f3])).
% 2.18/0.75  fof(f3,axiom,(
% 2.18/0.75    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.18/0.75  fof(f54,plain,(
% 2.18/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.18/0.75    inference(definition_unfolding,[],[f42,f51])).
% 2.18/0.75  fof(f42,plain,(
% 2.18/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.18/0.75    inference(cnf_transformation,[],[f25])).
% 2.18/0.75  fof(f25,plain,(
% 2.18/0.75    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.75    inference(ennf_transformation,[],[f6])).
% 2.18/0.75  fof(f6,axiom,(
% 2.18/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.18/0.75  fof(f1874,plain,(
% 2.18/0.75    spl3_26 | ~spl3_23),
% 2.18/0.75    inference(avatar_split_clause,[],[f1837,f840,f903])).
% 2.18/0.75  fof(f1837,plain,(
% 2.18/0.75    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_23),
% 2.18/0.75    inference(superposition,[],[f89,f842])).
% 2.18/0.75  fof(f89,plain,(
% 2.18/0.75    ( ! [X0,X1] : (m1_subset_1(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))),k1_zfmisc_1(X0))) )),
% 2.18/0.75    inference(resolution,[],[f85,f44])).
% 2.18/0.75  fof(f85,plain,(
% 2.18/0.75    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))),X0)) )),
% 2.18/0.75    inference(superposition,[],[f52,f38])).
% 2.18/0.75  fof(f1823,plain,(
% 2.18/0.75    spl3_23 | spl3_22),
% 2.18/0.75    inference(avatar_split_clause,[],[f1822,f836,f840])).
% 2.18/0.75  fof(f836,plain,(
% 2.18/0.75    spl3_22 <=> r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1)),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.18/0.75  fof(f1822,plain,(
% 2.18/0.75    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | spl3_22),
% 2.18/0.75    inference(forward_demodulation,[],[f1818,f38])).
% 2.18/0.75  fof(f1818,plain,(
% 2.18/0.75    sK1 = k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) | spl3_22),
% 2.18/0.75    inference(resolution,[],[f838,f153])).
% 2.18/0.75  fof(f153,plain,(
% 2.18/0.75    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X0,X1)) = X1) )),
% 2.18/0.75    inference(factoring,[],[f58])).
% 2.18/0.75  fof(f58,plain,(
% 2.18/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 2.18/0.75    inference(definition_unfolding,[],[f47,f39])).
% 2.18/0.75  fof(f47,plain,(
% 2.18/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.18/0.75    inference(cnf_transformation,[],[f1])).
% 2.18/0.75  fof(f1,axiom,(
% 2.18/0.75    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.18/0.75  fof(f838,plain,(
% 2.18/0.75    ~r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1) | spl3_22),
% 2.18/0.75    inference(avatar_component_clause,[],[f836])).
% 2.18/0.75  fof(f1787,plain,(
% 2.18/0.75    spl3_5 | ~spl3_4),
% 2.18/0.75    inference(avatar_split_clause,[],[f1786,f80,f106])).
% 2.18/0.75  fof(f106,plain,(
% 2.18/0.75    spl3_5 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.18/0.75  fof(f80,plain,(
% 2.18/0.75    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.18/0.75  fof(f1786,plain,(
% 2.18/0.75    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | ~spl3_4),
% 2.18/0.75    inference(forward_demodulation,[],[f1783,f38])).
% 2.18/0.75  fof(f1783,plain,(
% 2.18/0.75    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) | ~spl3_4),
% 2.18/0.75    inference(resolution,[],[f82,f54])).
% 2.18/0.75  fof(f82,plain,(
% 2.18/0.75    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 2.18/0.75    inference(avatar_component_clause,[],[f80])).
% 2.18/0.75  fof(f1785,plain,(
% 2.18/0.75    spl3_8 | ~spl3_1 | ~spl3_4),
% 2.18/0.75    inference(avatar_split_clause,[],[f1780,f80,f65,f178])).
% 2.18/0.75  fof(f178,plain,(
% 2.18/0.75    spl3_8 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.18/0.75  fof(f1780,plain,(
% 2.18/0.75    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl3_4),
% 2.18/0.75    inference(resolution,[],[f82,f32])).
% 2.18/0.75  fof(f32,plain,(
% 2.18/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.18/0.75    inference(cnf_transformation,[],[f20])).
% 2.18/0.75  fof(f20,plain,(
% 2.18/0.75    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.75    inference(ennf_transformation,[],[f11])).
% 2.18/0.75  fof(f11,axiom,(
% 2.18/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 2.18/0.75  fof(f942,plain,(
% 2.18/0.75    ~spl3_31 | spl3_18 | ~spl3_24),
% 2.18/0.75    inference(avatar_split_clause,[],[f924,f892,f425,f939])).
% 2.18/0.75  fof(f425,plain,(
% 2.18/0.75    spl3_18 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.18/0.75  fof(f892,plain,(
% 2.18/0.75    spl3_24 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.18/0.75  fof(f924,plain,(
% 2.18/0.75    ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | (spl3_18 | ~spl3_24)),
% 2.18/0.75    inference(backward_demodulation,[],[f427,f894])).
% 2.18/0.75  fof(f894,plain,(
% 2.18/0.75    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) | ~spl3_24),
% 2.18/0.75    inference(avatar_component_clause,[],[f892])).
% 2.18/0.75  fof(f427,plain,(
% 2.18/0.75    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl3_18),
% 2.18/0.75    inference(avatar_component_clause,[],[f425])).
% 2.18/0.75  fof(f895,plain,(
% 2.18/0.75    spl3_24 | ~spl3_5 | ~spl3_23),
% 2.18/0.75    inference(avatar_split_clause,[],[f859,f840,f106,f892])).
% 2.18/0.75  fof(f859,plain,(
% 2.18/0.75    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) | (~spl3_5 | ~spl3_23)),
% 2.18/0.75    inference(backward_demodulation,[],[f108,f842])).
% 2.18/0.75  fof(f108,plain,(
% 2.18/0.75    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) | ~spl3_5),
% 2.18/0.75    inference(avatar_component_clause,[],[f106])).
% 2.18/0.75  fof(f843,plain,(
% 2.18/0.75    ~spl3_22 | spl3_23 | ~spl3_4),
% 2.18/0.75    inference(avatar_split_clause,[],[f834,f80,f840,f836])).
% 2.18/0.75  fof(f834,plain,(
% 2.18/0.75    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | ~r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1) | ~spl3_4),
% 2.18/0.75    inference(forward_demodulation,[],[f833,f38])).
% 2.18/0.75  fof(f833,plain,(
% 2.18/0.75    sK1 = k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) | ~r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1) | ~spl3_4),
% 2.18/0.75    inference(duplicate_literal_removal,[],[f823])).
% 2.18/0.75  fof(f823,plain,(
% 2.18/0.75    sK1 = k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) | ~r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1) | ~r2_hidden(sK2(u1_struct_0(sK0),sK1,sK1),sK1) | sK1 = k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)) | ~spl3_4),
% 2.18/0.75    inference(resolution,[],[f213,f60])).
% 2.18/0.75  fof(f60,plain,(
% 2.18/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 2.18/0.75    inference(definition_unfolding,[],[f45,f39])).
% 2.18/0.75  fof(f45,plain,(
% 2.18/0.75    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.18/0.75    inference(cnf_transformation,[],[f1])).
% 2.18/0.75  fof(f213,plain,(
% 2.18/0.75    ( ! [X16] : (r2_hidden(sK2(X16,sK1,sK1),u1_struct_0(sK0)) | sK1 = k1_setfam_1(k2_tarski(X16,sK1))) ) | ~spl3_4),
% 2.18/0.75    inference(resolution,[],[f153,f96])).
% 2.18/0.75  fof(f96,plain,(
% 2.18/0.75    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0))) ) | ~spl3_4),
% 2.18/0.75    inference(resolution,[],[f43,f82])).
% 2.18/0.75  fof(f43,plain,(
% 2.18/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.18/0.75    inference(cnf_transformation,[],[f26])).
% 2.18/0.75  fof(f26,plain,(
% 2.18/0.75    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/0.75    inference(ennf_transformation,[],[f7])).
% 2.18/0.75  fof(f7,axiom,(
% 2.18/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 2.18/0.75  fof(f442,plain,(
% 2.18/0.75    spl3_21 | ~spl3_10),
% 2.18/0.75    inference(avatar_split_clause,[],[f412,f239,f439])).
% 2.18/0.75  fof(f439,plain,(
% 2.18/0.75    spl3_21 <=> k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.18/0.75  fof(f239,plain,(
% 2.18/0.75    spl3_10 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.18/0.75  fof(f412,plain,(
% 2.18/0.75    k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_10),
% 2.18/0.75    inference(resolution,[],[f241,f54])).
% 2.18/0.75  fof(f241,plain,(
% 2.18/0.75    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_10),
% 2.18/0.75    inference(avatar_component_clause,[],[f239])).
% 2.18/0.75  fof(f437,plain,(
% 2.18/0.75    spl3_20 | ~spl3_18 | ~spl3_1 | ~spl3_10),
% 2.18/0.75    inference(avatar_split_clause,[],[f411,f239,f65,f425,f434])).
% 2.18/0.75  fof(f434,plain,(
% 2.18/0.75    spl3_20 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.18/0.75  fof(f411,plain,(
% 2.18/0.75    ~l1_pre_topc(sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl3_10),
% 2.18/0.75    inference(resolution,[],[f241,f34])).
% 2.18/0.75  fof(f34,plain,(
% 2.18/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 2.18/0.75    inference(cnf_transformation,[],[f23])).
% 2.18/0.75  fof(f23,plain,(
% 2.18/0.75    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.75    inference(flattening,[],[f22])).
% 2.18/0.75  fof(f22,plain,(
% 2.18/0.75    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.75    inference(ennf_transformation,[],[f17])).
% 2.18/0.75  fof(f17,plain,(
% 2.18/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 2.18/0.75    inference(pure_predicate_removal,[],[f10])).
% 2.18/0.75  fof(f10,axiom,(
% 2.18/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.18/0.75  fof(f295,plain,(
% 2.18/0.75    spl3_15 | ~spl3_5),
% 2.18/0.75    inference(avatar_split_clause,[],[f286,f106,f292])).
% 2.18/0.75  fof(f292,plain,(
% 2.18/0.75    spl3_15 <=> k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.18/0.75  fof(f286,plain,(
% 2.18/0.75    k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl3_5),
% 2.18/0.75    inference(superposition,[],[f129,f108])).
% 2.18/0.75  fof(f129,plain,(
% 2.18/0.75    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))))))) )),
% 2.18/0.75    inference(superposition,[],[f53,f38])).
% 2.18/0.75  fof(f242,plain,(
% 2.18/0.75    spl3_10 | ~spl3_5),
% 2.18/0.75    inference(avatar_split_clause,[],[f236,f106,f239])).
% 2.18/0.75  fof(f236,plain,(
% 2.18/0.75    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 2.18/0.75    inference(superposition,[],[f89,f108])).
% 2.18/0.75  fof(f198,plain,(
% 2.18/0.75    spl3_9 | ~spl3_1 | ~spl3_4),
% 2.18/0.75    inference(avatar_split_clause,[],[f189,f80,f65,f195])).
% 2.18/0.75  fof(f195,plain,(
% 2.18/0.75    spl3_9 <=> k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.18/0.75  fof(f189,plain,(
% 2.18/0.75    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) | ~spl3_4),
% 2.18/0.75    inference(resolution,[],[f33,f82])).
% 2.18/0.75  fof(f33,plain,(
% 2.18/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))) )),
% 2.18/0.75    inference(cnf_transformation,[],[f21])).
% 2.18/0.75  fof(f21,plain,(
% 2.18/0.75    ! [X0] : (! [X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/0.75    inference(ennf_transformation,[],[f13])).
% 2.18/0.75  fof(f13,axiom,(
% 2.18/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_1)).
% 2.18/0.75  fof(f83,plain,(
% 2.18/0.75    spl3_4),
% 2.18/0.75    inference(avatar_split_clause,[],[f28,f80])).
% 2.18/0.75  fof(f28,plain,(
% 2.18/0.75    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/0.75    inference(cnf_transformation,[],[f19])).
% 2.18/0.75  fof(f19,plain,(
% 2.18/0.75    ? [X0] : (? [X1] : (k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.18/0.75    inference(flattening,[],[f18])).
% 2.18/0.75  fof(f18,plain,(
% 2.18/0.75    ? [X0] : (? [X1] : ((k2_pre_topc(X0,X1) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) & v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.18/0.75    inference(ennf_transformation,[],[f15])).
% 2.18/0.75  fof(f15,negated_conjecture,(
% 2.18/0.75    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 2.18/0.75    inference(negated_conjecture,[],[f14])).
% 2.18/0.75  fof(f14,conjecture,(
% 2.18/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 2.18/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tops_1)).
% 2.18/0.75  fof(f78,plain,(
% 2.18/0.75    spl3_3),
% 2.18/0.75    inference(avatar_split_clause,[],[f29,f75])).
% 2.18/0.75  fof(f29,plain,(
% 2.18/0.75    v3_pre_topc(sK1,sK0)),
% 2.18/0.75    inference(cnf_transformation,[],[f19])).
% 2.18/0.75  fof(f73,plain,(
% 2.18/0.75    ~spl3_2),
% 2.18/0.75    inference(avatar_split_clause,[],[f30,f70])).
% 2.18/0.75  fof(f70,plain,(
% 2.18/0.75    spl3_2 <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 2.18/0.75    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.18/0.75  fof(f30,plain,(
% 2.18/0.75    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 2.18/0.75    inference(cnf_transformation,[],[f19])).
% 2.18/0.75  fof(f68,plain,(
% 2.18/0.75    spl3_1),
% 2.18/0.75    inference(avatar_split_clause,[],[f31,f65])).
% 2.18/0.75  fof(f31,plain,(
% 2.18/0.75    l1_pre_topc(sK0)),
% 2.18/0.75    inference(cnf_transformation,[],[f19])).
% 2.18/0.75  % SZS output end Proof for theBenchmark
% 2.18/0.75  % (15252)------------------------------
% 2.18/0.75  % (15252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.75  % (15252)Termination reason: Refutation
% 2.18/0.75  
% 2.18/0.75  % (15252)Memory used [KB]: 12409
% 2.18/0.75  % (15252)Time elapsed: 0.325 s
% 2.18/0.75  % (15252)------------------------------
% 2.18/0.75  % (15252)------------------------------
% 2.18/0.75  % (15296)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.18/0.75  % (15299)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.18/0.75  % (15235)Success in time 0.381 s
%------------------------------------------------------------------------------
