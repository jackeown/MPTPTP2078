%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:37 EST 2020

% Result     : Theorem 3.37s
% Output     : Refutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 476 expanded)
%              Number of leaves         :   44 ( 160 expanded)
%              Depth                    :   13
%              Number of atoms          :  666 (1468 expanded)
%              Number of equality atoms :  111 ( 289 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3696,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f115,f120,f125,f130,f136,f253,f563,f759,f917,f966,f1014,f1022,f1135,f2007,f2101,f2107,f2115,f2147,f2149,f2247,f3645,f3688,f3695])).

fof(f3695,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3688,plain,
    ( spl2_42
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_154 ),
    inference(avatar_split_clause,[],[f3687,f3642,f122,f117,f980])).

fof(f980,plain,
    ( spl2_42
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f117,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f122,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f3642,plain,
    ( spl2_154
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_154])])).

fof(f3687,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_154 ),
    inference(subsumption_resolution,[],[f3686,f124])).

fof(f124,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f3686,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_154 ),
    inference(subsumption_resolution,[],[f3657,f119])).

fof(f119,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f3657,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_154 ),
    inference(superposition,[],[f276,f3644])).

fof(f3644,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_154 ),
    inference(avatar_component_clause,[],[f3642])).

fof(f276,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f73,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f73,plain,(
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

fof(f3645,plain,
    ( spl2_52
    | spl2_154
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f3640,f663,f658,f3642,f1102])).

fof(f1102,plain,
    ( spl2_52
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f658,plain,
    ( spl2_30
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f663,plain,
    ( spl2_31
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f3640,plain,
    ( ! [X17] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(subsumption_resolution,[],[f3597,f660])).

fof(f660,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f658])).

fof(f3597,plain,
    ( ! [X17] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_31 ),
    inference(superposition,[],[f792,f665])).

fof(f665,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f663])).

fof(f792,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f787,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f787,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f298,f73])).

fof(f298,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f294,f89])).

fof(f294,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f80,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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

fof(f2247,plain,(
    ~ spl2_52 ),
    inference(avatar_contradiction_clause,[],[f2223])).

fof(f2223,plain,
    ( $false
    | ~ spl2_52 ),
    inference(unit_resulting_resolution,[],[f1328,f1328,f1103,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1103,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f1102])).

fof(f1328,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f1325,f104])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
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

fof(f1325,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f442,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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

fof(f442,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X4))
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4)) ) ),
    inference(superposition,[],[f219,f138])).

fof(f138,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f96,f101])).

fof(f101,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f96,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f219,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f89,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2149,plain,
    ( spl2_31
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f2148,f654,f230,f663])).

fof(f230,plain,
    ( spl2_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f654,plain,
    ( spl2_29
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f2148,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f2133,f655])).

fof(f655,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f654])).

fof(f2133,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f220,f232])).

fof(f232,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f230])).

fof(f220,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f77,f78])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2147,plain,
    ( spl2_30
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f2146,f654,f230,f658])).

fof(f2146,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(subsumption_resolution,[],[f2132,f655])).

fof(f2132,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f219,f232])).

fof(f2115,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f2114,f226,f111,f230])).

fof(f111,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f226,plain,
    ( spl2_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f2114,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f2111,f227])).

fof(f227,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f226])).

fof(f2111,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f73,f112])).

fof(f112,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f2107,plain,
    ( ~ spl2_1
    | spl2_42
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f2047,f976,f133,f122,f117,f980,f107])).

fof(f107,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f133,plain,
    ( spl2_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f976,plain,
    ( spl2_41
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f2047,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f2046,f135])).

fof(f135,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f2046,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_41 ),
    inference(subsumption_resolution,[],[f2044,f104])).

fof(f2044,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_41 ),
    inference(resolution,[],[f977,f334])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | k1_tops_1(sK0,sK1) = X0
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f309,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f309,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f308,f88])).

fof(f308,plain,
    ( ! [X13] :
        ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X13,sK0)
        | r1_tarski(X13,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X13,sK1) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f306,f124])).

fof(f306,plain,
    ( ! [X13] :
        ( ~ r1_tarski(X13,sK1)
        | ~ v3_pre_topc(X13,sK0)
        | r1_tarski(X13,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f86,f119])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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

fof(f977,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f976])).

fof(f2101,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_10
    | ~ spl2_42 ),
    inference(avatar_contradiction_clause,[],[f2100])).

fof(f2100,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10
    | ~ spl2_42 ),
    inference(subsumption_resolution,[],[f2099,f124])).

fof(f2099,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_10
    | ~ spl2_42 ),
    inference(subsumption_resolution,[],[f2098,f119])).

fof(f2098,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_10
    | ~ spl2_42 ),
    inference(subsumption_resolution,[],[f2094,f231])).

fof(f231,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f230])).

fof(f2094,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_42 ),
    inference(superposition,[],[f885,f982])).

fof(f982,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f980])).

fof(f885,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f300,f291])).

fof(f291,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f284,f84])).

fof(f84,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f284,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f100,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f300,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f81,f73])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f2007,plain,
    ( spl2_41
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f2006,f122,f117,f976])).

fof(f2006,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1995,f124])).

fof(f1995,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f713,f119])).

fof(f713,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12)))
      | r1_tarski(k1_tops_1(X12,X11),X11)
      | ~ l1_pre_topc(X12) ) ),
    inference(superposition,[],[f97,f276])).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1135,plain,
    ( spl2_38
    | ~ spl2_27
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f1134,f891,f644,f895])).

fof(f895,plain,
    ( spl2_38
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f644,plain,
    ( spl2_27
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f891,plain,
    ( spl2_37
  <=> r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f1134,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_27
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f1132,f646])).

fof(f646,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f644])).

fof(f1132,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_37 ),
    inference(resolution,[],[f892,f76])).

fof(f892,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f891])).

fof(f1022,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_27 ),
    inference(avatar_contradiction_clause,[],[f1021])).

fof(f1021,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_27 ),
    inference(subsumption_resolution,[],[f1020,f124])).

fof(f1020,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_27 ),
    inference(subsumption_resolution,[],[f1019,f119])).

fof(f1019,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(subsumption_resolution,[],[f1018,f104])).

fof(f1018,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_27 ),
    inference(superposition,[],[f645,f289])).

fof(f289,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f286,f84])).

fof(f286,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f83,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f645,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f644])).

fof(f1014,plain,
    ( ~ spl2_10
    | spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f1013,f226,f111,f230])).

fof(f1013,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f1012,f227])).

fof(f1012,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f113,f73])).

fof(f113,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f966,plain,
    ( spl2_35
    | ~ spl2_38 ),
    inference(avatar_contradiction_clause,[],[f965])).

fof(f965,plain,
    ( $false
    | spl2_35
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f952,f758])).

fof(f758,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_35 ),
    inference(avatar_component_clause,[],[f756])).

fof(f756,plain,
    ( spl2_35
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f952,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_38 ),
    inference(superposition,[],[f141,f897])).

fof(f897,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f895])).

fof(f141,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f92,f96])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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

fof(f917,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_37 ),
    inference(avatar_contradiction_clause,[],[f916])).

fof(f916,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_37 ),
    inference(subsumption_resolution,[],[f915,f124])).

fof(f915,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_37 ),
    inference(subsumption_resolution,[],[f914,f119])).

fof(f914,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_37 ),
    inference(subsumption_resolution,[],[f913,f104])).

fof(f913,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_37 ),
    inference(superposition,[],[f893,f289])).

fof(f893,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | spl2_37 ),
    inference(avatar_component_clause,[],[f891])).

fof(f759,plain,
    ( ~ spl2_35
    | spl2_29 ),
    inference(avatar_split_clause,[],[f754,f654,f756])).

fof(f754,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_29 ),
    inference(resolution,[],[f656,f88])).

fof(f656,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f654])).

fof(f563,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(subsumption_resolution,[],[f561,f124])).

fof(f561,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_9 ),
    inference(subsumption_resolution,[],[f553,f119])).

fof(f553,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(resolution,[],[f291,f228])).

fof(f228,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f226])).

fof(f253,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f248,f127,f122,f117,f250])).

fof(f250,plain,
    ( spl2_12
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f127,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f248,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f247,f129])).

fof(f129,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f247,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f245,f124])).

fof(f245,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f85,f119])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f136,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f131,f117,f133])).

fof(f131,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f87,f119])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f130,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f68,f127])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f60,f62,f61])).

fof(f61,plain,
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

fof(f62,plain,
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

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
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

fof(f125,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f69,f122])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f120,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f70,f117])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f115,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f71,f111,f107])).

fof(f71,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f114,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f72,f111,f107])).

fof(f72,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (6310)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.49  % (6304)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (6313)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (6321)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (6303)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (6298)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (6324)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (6322)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (6299)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (6302)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (6312)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (6314)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (6308)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (6316)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (6328)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (6305)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (6307)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (6329)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (6315)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (6325)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (6319)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (6320)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (6323)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (6311)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (6300)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.58  % (6301)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.70/0.58  % (6327)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.70/0.59  % (6317)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.70/0.60  % (6318)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.88/0.60  % (6309)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 3.37/0.81  % (6323)Time limit reached!
% 3.37/0.81  % (6323)------------------------------
% 3.37/0.81  % (6323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.81  % (6323)Termination reason: Time limit
% 3.37/0.81  
% 3.37/0.81  % (6323)Memory used [KB]: 13176
% 3.37/0.81  % (6323)Time elapsed: 0.408 s
% 3.37/0.81  % (6323)------------------------------
% 3.37/0.81  % (6323)------------------------------
% 3.37/0.84  % (6300)Time limit reached!
% 3.37/0.84  % (6300)------------------------------
% 3.37/0.84  % (6300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.84  % (6300)Termination reason: Time limit
% 3.37/0.84  
% 3.37/0.84  % (6300)Memory used [KB]: 6396
% 3.37/0.84  % (6300)Time elapsed: 0.437 s
% 3.37/0.84  % (6300)------------------------------
% 3.37/0.84  % (6300)------------------------------
% 3.37/0.85  % (6320)Refutation found. Thanks to Tanya!
% 3.37/0.85  % SZS status Theorem for theBenchmark
% 3.37/0.85  % SZS output start Proof for theBenchmark
% 3.37/0.85  fof(f3696,plain,(
% 3.37/0.85    $false),
% 3.37/0.85    inference(avatar_sat_refutation,[],[f114,f115,f120,f125,f130,f136,f253,f563,f759,f917,f966,f1014,f1022,f1135,f2007,f2101,f2107,f2115,f2147,f2149,f2247,f3645,f3688,f3695])).
% 3.37/0.85  fof(f3695,plain,(
% 3.37/0.85    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.37/0.85    introduced(theory_tautology_sat_conflict,[])).
% 3.37/0.85  fof(f3688,plain,(
% 3.37/0.85    spl2_42 | ~spl2_3 | ~spl2_4 | ~spl2_154),
% 3.37/0.85    inference(avatar_split_clause,[],[f3687,f3642,f122,f117,f980])).
% 3.37/0.85  fof(f980,plain,(
% 3.37/0.85    spl2_42 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 3.37/0.85  fof(f117,plain,(
% 3.37/0.85    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.37/0.85  fof(f122,plain,(
% 3.37/0.85    spl2_4 <=> l1_pre_topc(sK0)),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.37/0.85  fof(f3642,plain,(
% 3.37/0.85    spl2_154 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_154])])).
% 3.37/0.85  fof(f3687,plain,(
% 3.37/0.85    sK1 = k1_tops_1(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_154)),
% 3.37/0.85    inference(subsumption_resolution,[],[f3686,f124])).
% 3.37/0.85  fof(f124,plain,(
% 3.37/0.85    l1_pre_topc(sK0) | ~spl2_4),
% 3.37/0.85    inference(avatar_component_clause,[],[f122])).
% 3.37/0.85  fof(f3686,plain,(
% 3.37/0.85    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_154)),
% 3.37/0.85    inference(subsumption_resolution,[],[f3657,f119])).
% 3.37/0.85  fof(f119,plain,(
% 3.37/0.85    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.37/0.85    inference(avatar_component_clause,[],[f117])).
% 3.37/0.85  fof(f3657,plain,(
% 3.37/0.85    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_154),
% 3.37/0.85    inference(superposition,[],[f276,f3644])).
% 3.37/0.85  fof(f3644,plain,(
% 3.37/0.85    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_154),
% 3.37/0.85    inference(avatar_component_clause,[],[f3642])).
% 3.37/0.85  fof(f276,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.37/0.85    inference(duplicate_literal_removal,[],[f275])).
% 3.37/0.85  fof(f275,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.37/0.85    inference(superposition,[],[f73,f82])).
% 3.37/0.85  fof(f82,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f42])).
% 3.37/0.85  fof(f42,plain,(
% 3.37/0.85    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.37/0.85    inference(ennf_transformation,[],[f31])).
% 3.37/0.85  fof(f31,axiom,(
% 3.37/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 3.37/0.85  fof(f73,plain,(
% 3.37/0.85    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(cnf_transformation,[],[f36])).
% 3.37/0.85  fof(f36,plain,(
% 3.37/0.85    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.37/0.85    inference(ennf_transformation,[],[f21])).
% 3.37/0.85  fof(f21,axiom,(
% 3.37/0.85    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.37/0.85  fof(f3645,plain,(
% 3.37/0.85    spl2_52 | spl2_154 | ~spl2_30 | ~spl2_31),
% 3.37/0.85    inference(avatar_split_clause,[],[f3640,f663,f658,f3642,f1102])).
% 3.37/0.85  fof(f1102,plain,(
% 3.37/0.85    spl2_52 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 3.37/0.85  fof(f658,plain,(
% 3.37/0.85    spl2_30 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 3.37/0.85  fof(f663,plain,(
% 3.37/0.85    spl2_31 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 3.37/0.85  fof(f3640,plain,(
% 3.37/0.85    ( ! [X17] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X17,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl2_30 | ~spl2_31)),
% 3.37/0.85    inference(subsumption_resolution,[],[f3597,f660])).
% 3.37/0.85  fof(f660,plain,(
% 3.37/0.85    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_30),
% 3.37/0.85    inference(avatar_component_clause,[],[f658])).
% 3.37/0.85  fof(f3597,plain,(
% 3.37/0.85    ( ! [X17] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X17,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_31),
% 3.37/0.85    inference(superposition,[],[f792,f665])).
% 3.37/0.85  fof(f665,plain,(
% 3.37/0.85    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_31),
% 3.37/0.85    inference(avatar_component_clause,[],[f663])).
% 3.37/0.85  fof(f792,plain,(
% 3.37/0.85    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 3.37/0.85    inference(subsumption_resolution,[],[f787,f89])).
% 3.37/0.85  fof(f89,plain,(
% 3.37/0.85    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(cnf_transformation,[],[f50])).
% 3.37/0.85  fof(f50,plain,(
% 3.37/0.85    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.37/0.85    inference(ennf_transformation,[],[f13])).
% 3.37/0.85  fof(f13,axiom,(
% 3.37/0.85    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.37/0.85  fof(f787,plain,(
% 3.37/0.85    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 3.37/0.85    inference(superposition,[],[f298,f73])).
% 3.37/0.85  fof(f298,plain,(
% 3.37/0.85    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.37/0.85    inference(subsumption_resolution,[],[f294,f89])).
% 3.37/0.85  fof(f294,plain,(
% 3.37/0.85    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.37/0.85    inference(superposition,[],[f80,f98])).
% 3.37/0.85  fof(f98,plain,(
% 3.37/0.85    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(cnf_transformation,[],[f54])).
% 3.37/0.85  fof(f54,plain,(
% 3.37/0.85    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.37/0.85    inference(ennf_transformation,[],[f16])).
% 3.37/0.85  fof(f16,axiom,(
% 3.37/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 3.37/0.85  fof(f80,plain,(
% 3.37/0.85    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(cnf_transformation,[],[f40])).
% 3.37/0.85  fof(f40,plain,(
% 3.37/0.85    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.37/0.85    inference(ennf_transformation,[],[f22])).
% 3.37/0.85  fof(f22,axiom,(
% 3.37/0.85    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 3.37/0.85  fof(f2247,plain,(
% 3.37/0.85    ~spl2_52),
% 3.37/0.85    inference(avatar_contradiction_clause,[],[f2223])).
% 3.37/0.85  fof(f2223,plain,(
% 3.37/0.85    $false | ~spl2_52),
% 3.37/0.85    inference(unit_resulting_resolution,[],[f1328,f1328,f1103,f100])).
% 3.37/0.85  fof(f100,plain,(
% 3.37/0.85    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(cnf_transformation,[],[f58])).
% 3.37/0.85  fof(f58,plain,(
% 3.37/0.85    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.37/0.85    inference(flattening,[],[f57])).
% 3.37/0.85  fof(f57,plain,(
% 3.37/0.85    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.37/0.85    inference(ennf_transformation,[],[f14])).
% 3.37/0.85  fof(f14,axiom,(
% 3.37/0.85    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.37/0.85  fof(f1103,plain,(
% 3.37/0.85    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_52),
% 3.37/0.85    inference(avatar_component_clause,[],[f1102])).
% 3.37/0.85  fof(f1328,plain,(
% 3.37/0.85    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(subsumption_resolution,[],[f1325,f104])).
% 3.37/0.85  fof(f104,plain,(
% 3.37/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.37/0.85    inference(equality_resolution,[],[f75])).
% 3.37/0.85  fof(f75,plain,(
% 3.37/0.85    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.37/0.85    inference(cnf_transformation,[],[f65])).
% 3.37/0.85  fof(f65,plain,(
% 3.37/0.85    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.37/0.85    inference(flattening,[],[f64])).
% 3.37/0.85  fof(f64,plain,(
% 3.37/0.85    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.37/0.85    inference(nnf_transformation,[],[f1])).
% 3.37/0.85  fof(f1,axiom,(
% 3.37/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.37/0.85  fof(f1325,plain,(
% 3.37/0.85    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~r1_tarski(X0,X0)) )),
% 3.37/0.85    inference(resolution,[],[f442,f88])).
% 3.37/0.85  fof(f88,plain,(
% 3.37/0.85    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f66])).
% 3.37/0.85  fof(f66,plain,(
% 3.37/0.85    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.37/0.85    inference(nnf_transformation,[],[f24])).
% 3.37/0.85  fof(f24,axiom,(
% 3.37/0.85    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.37/0.85  fof(f442,plain,(
% 3.37/0.85    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(X4)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4))) )),
% 3.37/0.85    inference(superposition,[],[f219,f138])).
% 3.37/0.85  fof(f138,plain,(
% 3.37/0.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.37/0.85    inference(superposition,[],[f96,f101])).
% 3.37/0.85  fof(f101,plain,(
% 3.37/0.85    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.37/0.85    inference(cnf_transformation,[],[f4])).
% 3.37/0.85  fof(f4,axiom,(
% 3.37/0.85    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 3.37/0.85  fof(f96,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.37/0.85    inference(cnf_transformation,[],[f9])).
% 3.37/0.85  fof(f9,axiom,(
% 3.37/0.85    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.37/0.85  fof(f219,plain,(
% 3.37/0.85    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 3.37/0.85    inference(duplicate_literal_removal,[],[f217])).
% 3.37/0.85  fof(f217,plain,(
% 3.37/0.85    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 3.37/0.85    inference(superposition,[],[f89,f78])).
% 3.37/0.85  fof(f78,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(cnf_transformation,[],[f38])).
% 3.37/0.85  fof(f38,plain,(
% 3.37/0.85    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.37/0.85    inference(ennf_transformation,[],[f12])).
% 3.37/0.85  fof(f12,axiom,(
% 3.37/0.85    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.37/0.85  fof(f2149,plain,(
% 3.37/0.85    spl2_31 | ~spl2_10 | ~spl2_29),
% 3.37/0.85    inference(avatar_split_clause,[],[f2148,f654,f230,f663])).
% 3.37/0.85  fof(f230,plain,(
% 3.37/0.85    spl2_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 3.37/0.85  fof(f654,plain,(
% 3.37/0.85    spl2_29 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 3.37/0.85  fof(f2148,plain,(
% 3.37/0.85    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_10 | ~spl2_29)),
% 3.37/0.85    inference(subsumption_resolution,[],[f2133,f655])).
% 3.37/0.85  fof(f655,plain,(
% 3.37/0.85    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_29),
% 3.37/0.85    inference(avatar_component_clause,[],[f654])).
% 3.37/0.85  fof(f2133,plain,(
% 3.37/0.85    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 3.37/0.85    inference(superposition,[],[f220,f232])).
% 3.37/0.85  fof(f232,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_10),
% 3.37/0.85    inference(avatar_component_clause,[],[f230])).
% 3.37/0.85  fof(f220,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(duplicate_literal_removal,[],[f216])).
% 3.37/0.85  fof(f216,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(superposition,[],[f77,f78])).
% 3.37/0.85  fof(f77,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(cnf_transformation,[],[f37])).
% 3.37/0.85  fof(f37,plain,(
% 3.37/0.85    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.37/0.85    inference(ennf_transformation,[],[f17])).
% 3.37/0.85  fof(f17,axiom,(
% 3.37/0.85    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.37/0.85  fof(f2147,plain,(
% 3.37/0.85    spl2_30 | ~spl2_10 | ~spl2_29),
% 3.37/0.85    inference(avatar_split_clause,[],[f2146,f654,f230,f658])).
% 3.37/0.85  fof(f2146,plain,(
% 3.37/0.85    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | (~spl2_10 | ~spl2_29)),
% 3.37/0.85    inference(subsumption_resolution,[],[f2132,f655])).
% 3.37/0.85  fof(f2132,plain,(
% 3.37/0.85    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 3.37/0.85    inference(superposition,[],[f219,f232])).
% 3.37/0.85  fof(f2115,plain,(
% 3.37/0.85    spl2_10 | ~spl2_2 | ~spl2_9),
% 3.37/0.85    inference(avatar_split_clause,[],[f2114,f226,f111,f230])).
% 3.37/0.85  fof(f111,plain,(
% 3.37/0.85    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.37/0.85  fof(f226,plain,(
% 3.37/0.85    spl2_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.37/0.85  fof(f2114,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_2 | ~spl2_9)),
% 3.37/0.85    inference(subsumption_resolution,[],[f2111,f227])).
% 3.37/0.85  fof(f227,plain,(
% 3.37/0.85    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 3.37/0.85    inference(avatar_component_clause,[],[f226])).
% 3.37/0.85  fof(f2111,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 3.37/0.85    inference(superposition,[],[f73,f112])).
% 3.37/0.85  fof(f112,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 3.37/0.85    inference(avatar_component_clause,[],[f111])).
% 3.37/0.85  fof(f2107,plain,(
% 3.37/0.85    ~spl2_1 | spl2_42 | ~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_41),
% 3.37/0.85    inference(avatar_split_clause,[],[f2047,f976,f133,f122,f117,f980,f107])).
% 3.37/0.85  fof(f107,plain,(
% 3.37/0.85    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.37/0.85  fof(f133,plain,(
% 3.37/0.85    spl2_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.37/0.85  fof(f976,plain,(
% 3.37/0.85    spl2_41 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 3.37/0.85  fof(f2047,plain,(
% 3.37/0.85    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_41)),
% 3.37/0.85    inference(subsumption_resolution,[],[f2046,f135])).
% 3.37/0.85  fof(f135,plain,(
% 3.37/0.85    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_6),
% 3.37/0.85    inference(avatar_component_clause,[],[f133])).
% 3.37/0.85  fof(f2046,plain,(
% 3.37/0.85    ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_41)),
% 3.37/0.85    inference(subsumption_resolution,[],[f2044,f104])).
% 3.37/0.85  fof(f2044,plain,(
% 3.37/0.85    ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_41)),
% 3.37/0.85    inference(resolution,[],[f977,f334])).
% 3.37/0.85  fof(f334,plain,(
% 3.37/0.85    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0)) | k1_tops_1(sK0,sK1) = X0 | ~v3_pre_topc(X0,sK0)) ) | (~spl2_3 | ~spl2_4)),
% 3.37/0.85    inference(resolution,[],[f309,f76])).
% 3.37/0.85  fof(f76,plain,(
% 3.37/0.85    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f65])).
% 3.37/0.85  fof(f309,plain,(
% 3.37/0.85    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl2_3 | ~spl2_4)),
% 3.37/0.85    inference(resolution,[],[f308,f88])).
% 3.37/0.85  fof(f308,plain,(
% 3.37/0.85    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X13,sK0) | r1_tarski(X13,k1_tops_1(sK0,sK1)) | ~r1_tarski(X13,sK1)) ) | (~spl2_3 | ~spl2_4)),
% 3.37/0.85    inference(subsumption_resolution,[],[f306,f124])).
% 3.37/0.85  fof(f306,plain,(
% 3.37/0.85    ( ! [X13] : (~r1_tarski(X13,sK1) | ~v3_pre_topc(X13,sK0) | r1_tarski(X13,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_3),
% 3.37/0.85    inference(resolution,[],[f86,f119])).
% 3.37/0.85  fof(f86,plain,(
% 3.37/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f49])).
% 3.37/0.85  fof(f49,plain,(
% 3.37/0.85    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.37/0.85    inference(flattening,[],[f48])).
% 3.37/0.85  fof(f48,plain,(
% 3.37/0.85    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.37/0.85    inference(ennf_transformation,[],[f28])).
% 3.37/0.85  fof(f28,axiom,(
% 3.37/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 3.37/0.85  fof(f977,plain,(
% 3.37/0.85    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_41),
% 3.37/0.85    inference(avatar_component_clause,[],[f976])).
% 3.37/0.85  fof(f2101,plain,(
% 3.37/0.85    ~spl2_3 | ~spl2_4 | spl2_10 | ~spl2_42),
% 3.37/0.85    inference(avatar_contradiction_clause,[],[f2100])).
% 3.37/0.85  fof(f2100,plain,(
% 3.37/0.85    $false | (~spl2_3 | ~spl2_4 | spl2_10 | ~spl2_42)),
% 3.37/0.85    inference(subsumption_resolution,[],[f2099,f124])).
% 3.37/0.85  fof(f2099,plain,(
% 3.37/0.85    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_10 | ~spl2_42)),
% 3.37/0.85    inference(subsumption_resolution,[],[f2098,f119])).
% 3.37/0.85  fof(f2098,plain,(
% 3.37/0.85    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_10 | ~spl2_42)),
% 3.37/0.85    inference(subsumption_resolution,[],[f2094,f231])).
% 3.37/0.85  fof(f231,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl2_10),
% 3.37/0.85    inference(avatar_component_clause,[],[f230])).
% 3.37/0.85  fof(f2094,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_42),
% 3.37/0.85    inference(superposition,[],[f885,f982])).
% 3.37/0.85  fof(f982,plain,(
% 3.37/0.85    sK1 = k1_tops_1(sK0,sK1) | ~spl2_42),
% 3.37/0.85    inference(avatar_component_clause,[],[f980])).
% 3.37/0.85  fof(f885,plain,(
% 3.37/0.85    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.37/0.85    inference(subsumption_resolution,[],[f300,f291])).
% 3.37/0.85  fof(f291,plain,(
% 3.37/0.85    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.37/0.85    inference(subsumption_resolution,[],[f284,f84])).
% 3.37/0.85  fof(f84,plain,(
% 3.37/0.85    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f45])).
% 3.37/0.85  fof(f45,plain,(
% 3.37/0.85    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.37/0.85    inference(flattening,[],[f44])).
% 3.37/0.85  fof(f44,plain,(
% 3.37/0.85    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.37/0.85    inference(ennf_transformation,[],[f25])).
% 3.37/0.85  fof(f25,axiom,(
% 3.37/0.85    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.37/0.85  fof(f284,plain,(
% 3.37/0.85    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.37/0.85    inference(duplicate_literal_removal,[],[f283])).
% 3.37/0.85  fof(f283,plain,(
% 3.37/0.85    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.37/0.85    inference(superposition,[],[f100,f83])).
% 3.37/0.85  fof(f83,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f43])).
% 3.37/0.85  fof(f43,plain,(
% 3.37/0.85    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.37/0.85    inference(ennf_transformation,[],[f30])).
% 3.37/0.85  fof(f30,axiom,(
% 3.37/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 3.37/0.85  fof(f300,plain,(
% 3.37/0.85    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.37/0.85    inference(superposition,[],[f81,f73])).
% 3.37/0.85  fof(f81,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f41])).
% 3.37/0.85  fof(f41,plain,(
% 3.37/0.85    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.37/0.85    inference(ennf_transformation,[],[f27])).
% 3.37/0.85  fof(f27,axiom,(
% 3.37/0.85    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 3.37/0.85  fof(f2007,plain,(
% 3.37/0.85    spl2_41 | ~spl2_3 | ~spl2_4),
% 3.37/0.85    inference(avatar_split_clause,[],[f2006,f122,f117,f976])).
% 3.37/0.85  fof(f2006,plain,(
% 3.37/0.85    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 3.37/0.85    inference(subsumption_resolution,[],[f1995,f124])).
% 3.37/0.85  fof(f1995,plain,(
% 3.37/0.85    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 3.37/0.85    inference(resolution,[],[f713,f119])).
% 3.37/0.85  fof(f713,plain,(
% 3.37/0.85    ( ! [X12,X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X12))) | r1_tarski(k1_tops_1(X12,X11),X11) | ~l1_pre_topc(X12)) )),
% 3.37/0.85    inference(superposition,[],[f97,f276])).
% 3.37/0.85  fof(f97,plain,(
% 3.37/0.85    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f5])).
% 3.37/0.85  fof(f5,axiom,(
% 3.37/0.85    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.37/0.85  fof(f1135,plain,(
% 3.37/0.85    spl2_38 | ~spl2_27 | ~spl2_37),
% 3.37/0.85    inference(avatar_split_clause,[],[f1134,f891,f644,f895])).
% 3.37/0.85  fof(f895,plain,(
% 3.37/0.85    spl2_38 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 3.37/0.85  fof(f644,plain,(
% 3.37/0.85    spl2_27 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 3.37/0.85  fof(f891,plain,(
% 3.37/0.85    spl2_37 <=> r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 3.37/0.85  fof(f1134,plain,(
% 3.37/0.85    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_27 | ~spl2_37)),
% 3.37/0.85    inference(subsumption_resolution,[],[f1132,f646])).
% 3.37/0.85  fof(f646,plain,(
% 3.37/0.85    r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_27),
% 3.37/0.85    inference(avatar_component_clause,[],[f644])).
% 3.37/0.85  fof(f1132,plain,(
% 3.37/0.85    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl2_37),
% 3.37/0.85    inference(resolution,[],[f892,f76])).
% 3.37/0.85  fof(f892,plain,(
% 3.37/0.85    r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~spl2_37),
% 3.37/0.85    inference(avatar_component_clause,[],[f891])).
% 3.37/0.85  fof(f1022,plain,(
% 3.37/0.85    ~spl2_3 | ~spl2_4 | spl2_27),
% 3.37/0.85    inference(avatar_contradiction_clause,[],[f1021])).
% 3.37/0.85  fof(f1021,plain,(
% 3.37/0.85    $false | (~spl2_3 | ~spl2_4 | spl2_27)),
% 3.37/0.85    inference(subsumption_resolution,[],[f1020,f124])).
% 3.37/0.85  fof(f1020,plain,(
% 3.37/0.85    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_27)),
% 3.37/0.85    inference(subsumption_resolution,[],[f1019,f119])).
% 3.37/0.85  fof(f1019,plain,(
% 3.37/0.85    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_27),
% 3.37/0.85    inference(subsumption_resolution,[],[f1018,f104])).
% 3.37/0.85  fof(f1018,plain,(
% 3.37/0.85    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_27),
% 3.37/0.85    inference(superposition,[],[f645,f289])).
% 3.37/0.85  fof(f289,plain,(
% 3.37/0.85    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.37/0.85    inference(subsumption_resolution,[],[f286,f84])).
% 3.37/0.85  fof(f286,plain,(
% 3.37/0.85    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.37/0.85    inference(duplicate_literal_removal,[],[f281])).
% 3.37/0.85  fof(f281,plain,(
% 3.37/0.85    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.37/0.85    inference(superposition,[],[f83,f99])).
% 3.37/0.85  fof(f99,plain,(
% 3.37/0.85    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.37/0.85    inference(cnf_transformation,[],[f56])).
% 3.37/0.85  fof(f56,plain,(
% 3.37/0.85    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.37/0.85    inference(flattening,[],[f55])).
% 3.37/0.85  fof(f55,plain,(
% 3.37/0.85    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.37/0.85    inference(ennf_transformation,[],[f19])).
% 3.37/0.85  fof(f19,axiom,(
% 3.37/0.85    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.37/0.85  fof(f645,plain,(
% 3.37/0.85    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | spl2_27),
% 3.37/0.85    inference(avatar_component_clause,[],[f644])).
% 3.37/0.85  fof(f1014,plain,(
% 3.37/0.85    ~spl2_10 | spl2_2 | ~spl2_9),
% 3.37/0.85    inference(avatar_split_clause,[],[f1013,f226,f111,f230])).
% 3.37/0.85  fof(f1013,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl2_2 | ~spl2_9)),
% 3.37/0.85    inference(subsumption_resolution,[],[f1012,f227])).
% 3.37/0.85  fof(f1012,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 3.37/0.85    inference(superposition,[],[f113,f73])).
% 3.37/0.85  fof(f113,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 3.37/0.85    inference(avatar_component_clause,[],[f111])).
% 3.37/0.85  fof(f966,plain,(
% 3.37/0.85    spl2_35 | ~spl2_38),
% 3.37/0.85    inference(avatar_contradiction_clause,[],[f965])).
% 3.37/0.85  fof(f965,plain,(
% 3.37/0.85    $false | (spl2_35 | ~spl2_38)),
% 3.37/0.85    inference(subsumption_resolution,[],[f952,f758])).
% 3.37/0.85  fof(f758,plain,(
% 3.37/0.85    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_35),
% 3.37/0.85    inference(avatar_component_clause,[],[f756])).
% 3.37/0.85  fof(f756,plain,(
% 3.37/0.85    spl2_35 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 3.37/0.85  fof(f952,plain,(
% 3.37/0.85    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_38),
% 3.37/0.85    inference(superposition,[],[f141,f897])).
% 3.37/0.85  fof(f897,plain,(
% 3.37/0.85    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_38),
% 3.37/0.85    inference(avatar_component_clause,[],[f895])).
% 3.37/0.85  fof(f141,plain,(
% 3.37/0.85    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.37/0.85    inference(trivial_inequality_removal,[],[f140])).
% 3.37/0.85  fof(f140,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.37/0.85    inference(superposition,[],[f92,f96])).
% 3.37/0.85  fof(f92,plain,(
% 3.37/0.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f67])).
% 3.37/0.85  fof(f67,plain,(
% 3.37/0.85    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.37/0.85    inference(nnf_transformation,[],[f2])).
% 3.37/0.85  fof(f2,axiom,(
% 3.37/0.85    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.37/0.85  fof(f917,plain,(
% 3.37/0.85    ~spl2_3 | ~spl2_4 | spl2_37),
% 3.37/0.85    inference(avatar_contradiction_clause,[],[f916])).
% 3.37/0.85  fof(f916,plain,(
% 3.37/0.85    $false | (~spl2_3 | ~spl2_4 | spl2_37)),
% 3.37/0.85    inference(subsumption_resolution,[],[f915,f124])).
% 3.37/0.85  fof(f915,plain,(
% 3.37/0.85    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_37)),
% 3.37/0.85    inference(subsumption_resolution,[],[f914,f119])).
% 3.37/0.85  fof(f914,plain,(
% 3.37/0.85    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_37),
% 3.37/0.85    inference(subsumption_resolution,[],[f913,f104])).
% 3.37/0.85  fof(f913,plain,(
% 3.37/0.85    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_37),
% 3.37/0.85    inference(superposition,[],[f893,f289])).
% 3.37/0.85  fof(f893,plain,(
% 3.37/0.85    ~r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) | spl2_37),
% 3.37/0.85    inference(avatar_component_clause,[],[f891])).
% 3.37/0.85  fof(f759,plain,(
% 3.37/0.85    ~spl2_35 | spl2_29),
% 3.37/0.85    inference(avatar_split_clause,[],[f754,f654,f756])).
% 3.37/0.85  fof(f754,plain,(
% 3.37/0.85    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_29),
% 3.37/0.85    inference(resolution,[],[f656,f88])).
% 3.37/0.85  fof(f656,plain,(
% 3.37/0.85    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_29),
% 3.37/0.85    inference(avatar_component_clause,[],[f654])).
% 3.37/0.85  fof(f563,plain,(
% 3.37/0.85    ~spl2_3 | ~spl2_4 | spl2_9),
% 3.37/0.85    inference(avatar_contradiction_clause,[],[f562])).
% 3.37/0.85  fof(f562,plain,(
% 3.37/0.85    $false | (~spl2_3 | ~spl2_4 | spl2_9)),
% 3.37/0.85    inference(subsumption_resolution,[],[f561,f124])).
% 3.37/0.85  fof(f561,plain,(
% 3.37/0.85    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_9)),
% 3.37/0.85    inference(subsumption_resolution,[],[f553,f119])).
% 3.37/0.85  fof(f553,plain,(
% 3.37/0.85    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_9),
% 3.37/0.85    inference(resolution,[],[f291,f228])).
% 3.37/0.85  fof(f228,plain,(
% 3.37/0.85    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_9),
% 3.37/0.85    inference(avatar_component_clause,[],[f226])).
% 3.37/0.85  fof(f253,plain,(
% 3.37/0.85    spl2_12 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 3.37/0.85    inference(avatar_split_clause,[],[f248,f127,f122,f117,f250])).
% 3.37/0.85  fof(f250,plain,(
% 3.37/0.85    spl2_12 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 3.37/0.85  fof(f127,plain,(
% 3.37/0.85    spl2_5 <=> v2_pre_topc(sK0)),
% 3.37/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.37/0.85  fof(f248,plain,(
% 3.37/0.85    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 3.37/0.85    inference(subsumption_resolution,[],[f247,f129])).
% 3.37/0.85  fof(f129,plain,(
% 3.37/0.85    v2_pre_topc(sK0) | ~spl2_5),
% 3.37/0.85    inference(avatar_component_clause,[],[f127])).
% 3.37/0.85  fof(f247,plain,(
% 3.37/0.85    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl2_3 | ~spl2_4)),
% 3.37/0.85    inference(subsumption_resolution,[],[f245,f124])).
% 3.37/0.85  fof(f245,plain,(
% 3.37/0.85    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 3.37/0.85    inference(resolution,[],[f85,f119])).
% 3.37/0.85  fof(f85,plain,(
% 3.37/0.85    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f47])).
% 3.37/0.85  fof(f47,plain,(
% 3.37/0.85    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.37/0.85    inference(flattening,[],[f46])).
% 3.37/0.85  fof(f46,plain,(
% 3.37/0.85    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.37/0.85    inference(ennf_transformation,[],[f26])).
% 3.37/0.85  fof(f26,axiom,(
% 3.37/0.85    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.37/0.85  fof(f136,plain,(
% 3.37/0.85    spl2_6 | ~spl2_3),
% 3.37/0.85    inference(avatar_split_clause,[],[f131,f117,f133])).
% 3.37/0.85  fof(f131,plain,(
% 3.37/0.85    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 3.37/0.85    inference(resolution,[],[f87,f119])).
% 3.37/0.85  fof(f87,plain,(
% 3.37/0.85    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.37/0.85    inference(cnf_transformation,[],[f66])).
% 3.37/0.85  fof(f130,plain,(
% 3.37/0.85    spl2_5),
% 3.37/0.85    inference(avatar_split_clause,[],[f68,f127])).
% 3.37/0.85  fof(f68,plain,(
% 3.37/0.85    v2_pre_topc(sK0)),
% 3.37/0.85    inference(cnf_transformation,[],[f63])).
% 3.37/0.85  fof(f63,plain,(
% 3.37/0.85    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.37/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f60,f62,f61])).
% 3.37/0.85  fof(f61,plain,(
% 3.37/0.85    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.37/0.85    introduced(choice_axiom,[])).
% 3.37/0.85  fof(f62,plain,(
% 3.37/0.85    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.37/0.85    introduced(choice_axiom,[])).
% 3.37/0.85  fof(f60,plain,(
% 3.37/0.85    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.37/0.85    inference(flattening,[],[f59])).
% 3.37/0.85  fof(f59,plain,(
% 3.37/0.85    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.37/0.85    inference(nnf_transformation,[],[f35])).
% 3.37/0.85  fof(f35,plain,(
% 3.37/0.85    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.37/0.85    inference(flattening,[],[f34])).
% 3.37/0.85  fof(f34,plain,(
% 3.37/0.85    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.37/0.85    inference(ennf_transformation,[],[f33])).
% 3.37/0.85  fof(f33,negated_conjecture,(
% 3.37/0.85    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.37/0.85    inference(negated_conjecture,[],[f32])).
% 3.37/0.85  fof(f32,conjecture,(
% 3.37/0.85    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.37/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 3.37/0.85  fof(f125,plain,(
% 3.37/0.85    spl2_4),
% 3.37/0.85    inference(avatar_split_clause,[],[f69,f122])).
% 3.37/0.85  fof(f69,plain,(
% 3.37/0.85    l1_pre_topc(sK0)),
% 3.37/0.85    inference(cnf_transformation,[],[f63])).
% 3.37/0.85  fof(f120,plain,(
% 3.37/0.85    spl2_3),
% 3.37/0.85    inference(avatar_split_clause,[],[f70,f117])).
% 3.37/0.85  fof(f70,plain,(
% 3.37/0.85    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.37/0.85    inference(cnf_transformation,[],[f63])).
% 3.37/0.85  fof(f115,plain,(
% 3.37/0.85    spl2_1 | spl2_2),
% 3.37/0.85    inference(avatar_split_clause,[],[f71,f111,f107])).
% 3.37/0.85  fof(f71,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.37/0.85    inference(cnf_transformation,[],[f63])).
% 3.37/0.85  fof(f114,plain,(
% 3.37/0.85    ~spl2_1 | ~spl2_2),
% 3.37/0.85    inference(avatar_split_clause,[],[f72,f111,f107])).
% 3.37/0.85  fof(f72,plain,(
% 3.37/0.85    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.37/0.85    inference(cnf_transformation,[],[f63])).
% 3.37/0.85  % SZS output end Proof for theBenchmark
% 3.37/0.85  % (6320)------------------------------
% 3.37/0.85  % (6320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.85  % (6320)Termination reason: Refutation
% 3.37/0.85  
% 3.37/0.85  % (6320)Memory used [KB]: 8955
% 3.37/0.85  % (6320)Time elapsed: 0.416 s
% 3.37/0.85  % (6320)------------------------------
% 3.37/0.85  % (6320)------------------------------
% 3.37/0.85  % (6294)Success in time 0.493 s
%------------------------------------------------------------------------------
