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
% DateTime   : Thu Dec  3 13:11:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 356 expanded)
%              Number of leaves         :   47 ( 133 expanded)
%              Depth                    :   12
%              Number of atoms          :  579 (1115 expanded)
%              Number of equality atoms :   96 ( 225 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f932,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f100,f105,f110,f115,f188,f197,f227,f317,f363,f370,f372,f431,f460,f466,f692,f696,f712,f713,f781,f856,f874,f918,f931])).

fof(f931,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f918,plain,(
    ~ spl3_53 ),
    inference(avatar_contradiction_clause,[],[f917])).

fof(f917,plain,
    ( $false
    | ~ spl3_53 ),
    inference(resolution,[],[f776,f81])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f776,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f775])).

fof(f775,plain,
    ( spl3_53
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f874,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f873,f851,f107,f102,f210])).

fof(f210,plain,
    ( spl3_15
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f102,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f107,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f851,plain,
    ( spl3_56
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f873,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f872,f109])).

fof(f109,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f872,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f859,f104])).

fof(f104,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f859,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_56 ),
    inference(superposition,[],[f232,f853])).

fof(f853,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f851])).

fof(f232,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f63,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f856,plain,
    ( spl3_56
    | ~ spl3_39
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f855,f778,f453,f851])).

fof(f453,plain,
    ( spl3_39
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f778,plain,
    ( spl3_54
  <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f855,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_39
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f847,f454])).

fof(f454,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f453])).

fof(f847,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_54 ),
    inference(superposition,[],[f63,f780])).

fof(f780,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f778])).

fof(f781,plain,
    ( spl3_53
    | spl3_54
    | ~ spl3_40
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f773,f709,f457,f778,f775])).

fof(f457,plain,
    ( spl3_40
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f709,plain,
    ( spl3_50
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f773,plain,
    ( ! [X2] :
        ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_40
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f755,f459])).

fof(f459,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f457])).

fof(f755,plain,
    ( ! [X2] :
        ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_50 ),
    inference(superposition,[],[f265,f711])).

fof(f711,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f709])).

fof(f265,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f261,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f261,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f73,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f713,plain,
    ( spl3_41
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f700,f551,f463])).

fof(f463,plain,
    ( spl3_41
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f551,plain,
    ( spl3_47
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f700,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_47 ),
    inference(superposition,[],[f142,f553])).

fof(f553,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f551])).

fof(f142,plain,(
    ! [X0,X1] : r1_tarski(X1,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f138,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f138,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f83,f85])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f712,plain,
    ( ~ spl3_39
    | spl3_50
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f481,f199,f709,f453])).

fof(f199,plain,
    ( spl3_13
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f481,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_13 ),
    inference(superposition,[],[f154,f201])).

fof(f201,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f154,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f67,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f696,plain,
    ( spl3_47
    | ~ spl3_36
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f695,f547,f428,f551])).

fof(f428,plain,
    ( spl3_36
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f547,plain,
    ( spl3_46
  <=> r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f695,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_36
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f693,f430])).

fof(f430,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f428])).

fof(f693,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_46 ),
    inference(resolution,[],[f548,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f548,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f547])).

fof(f692,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_46 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_46 ),
    inference(subsumption_resolution,[],[f690,f109])).

fof(f690,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_46 ),
    inference(subsumption_resolution,[],[f689,f104])).

fof(f689,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_46 ),
    inference(subsumption_resolution,[],[f686,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f686,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_46 ),
    inference(superposition,[],[f549,f683])).

fof(f683,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f236,f272])).

fof(f272,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f269,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f269,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f72,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f236,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f86,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f549,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f547])).

fof(f466,plain,
    ( ~ spl3_41
    | spl3_39 ),
    inference(avatar_split_clause,[],[f461,f453,f463])).

fof(f461,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_39 ),
    inference(resolution,[],[f455,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f455,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f453])).

fof(f460,plain,
    ( ~ spl3_39
    | spl3_40
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f451,f199,f457,f453])).

fof(f451,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_13 ),
    inference(superposition,[],[f153,f201])).

fof(f153,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f80,f68])).

fof(f431,plain,
    ( spl3_36
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f426,f199,f428])).

fof(f426,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_13 ),
    inference(superposition,[],[f139,f201])).

fof(f139,plain,(
    ! [X2,X3] : r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3))) ),
    inference(resolution,[],[f83,f89])).

fof(f372,plain,
    ( ~ spl3_14
    | spl3_15
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f371,f185,f210,f206])).

fof(f206,plain,
    ( spl3_14
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f185,plain,
    ( spl3_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f371,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_12 ),
    inference(resolution,[],[f187,f66])).

fof(f187,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f370,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f369,f160,f96,f199])).

fof(f96,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f160,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f369,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f365,f161])).

fof(f161,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f365,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f63,f97])).

fof(f97,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f363,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f361,f109])).

fof(f361,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f360,f104])).

fof(f360,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_2
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f359,f98])).

fof(f98,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f359,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_15 ),
    inference(superposition,[],[f70,f212])).

fof(f212,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f210])).

fof(f317,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f109,f89,f208,f104,f104,f93,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f93,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f208,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f206])).

fof(f227,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f222,f112,f107,f102,f224])).

fof(f224,plain,
    ( spl3_16
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f112,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f222,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f221,f114])).

fof(f114,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f221,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f218,f109])).

fof(f218,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f76,f104])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f197,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f195,f109])).

fof(f195,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f190,f104])).

fof(f190,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f74,f162])).

fof(f162,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f188,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f183,f107,f102,f185])).

fof(f183,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f181,f109])).

fof(f181,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f82,f104])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f115,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f58,f112])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f50,plain,
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

fof(f51,plain,
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

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f110,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f59,f107])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f60,f102])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f61,f96,f92])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f99,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f62,f96,f92])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:12:37 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.52  % (19998)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (19991)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (19976)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (19990)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (19975)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (19983)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (19978)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (19977)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (19971)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (19972)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (19969)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (19997)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (19970)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (19996)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (19974)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (19973)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (19994)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (19995)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (19986)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (19985)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (19988)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (19989)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (19987)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (19984)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (19979)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (19981)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (19982)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (19992)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (19980)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (19993)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.57  % (19990)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f932,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f99,f100,f105,f110,f115,f188,f197,f227,f317,f363,f370,f372,f431,f460,f466,f692,f696,f712,f713,f781,f856,f874,f918,f931])).
% 0.22/0.59  fof(f931,plain,(
% 0.22/0.59    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.22/0.59    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.59  fof(f918,plain,(
% 0.22/0.59    ~spl3_53),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f917])).
% 0.22/0.59  fof(f917,plain,(
% 0.22/0.59    $false | ~spl3_53),
% 0.22/0.59    inference(resolution,[],[f776,f81])).
% 0.22/0.59  fof(f81,plain,(
% 0.22/0.59    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f57])).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f56])).
% 0.22/0.59  fof(f56,plain,(
% 0.22/0.59    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.59  fof(f776,plain,(
% 0.22/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_53),
% 0.22/0.59    inference(avatar_component_clause,[],[f775])).
% 0.22/0.59  fof(f775,plain,(
% 0.22/0.59    spl3_53 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.22/0.59  fof(f874,plain,(
% 0.22/0.59    spl3_15 | ~spl3_3 | ~spl3_4 | ~spl3_56),
% 0.22/0.59    inference(avatar_split_clause,[],[f873,f851,f107,f102,f210])).
% 0.22/0.59  fof(f210,plain,(
% 0.22/0.59    spl3_15 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.59  fof(f102,plain,(
% 0.22/0.59    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.59  fof(f107,plain,(
% 0.22/0.59    spl3_4 <=> l1_pre_topc(sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.59  fof(f851,plain,(
% 0.22/0.59    spl3_56 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.22/0.59  fof(f873,plain,(
% 0.22/0.59    sK1 = k1_tops_1(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_56)),
% 0.22/0.59    inference(subsumption_resolution,[],[f872,f109])).
% 0.22/0.59  fof(f109,plain,(
% 0.22/0.59    l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.59    inference(avatar_component_clause,[],[f107])).
% 0.22/0.59  fof(f872,plain,(
% 0.22/0.59    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_56)),
% 0.22/0.59    inference(subsumption_resolution,[],[f859,f104])).
% 0.22/0.59  fof(f104,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.22/0.59    inference(avatar_component_clause,[],[f102])).
% 0.22/0.59  fof(f859,plain,(
% 0.22/0.59    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_56),
% 0.22/0.59    inference(superposition,[],[f232,f853])).
% 0.22/0.59  fof(f853,plain,(
% 0.22/0.59    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_56),
% 0.22/0.59    inference(avatar_component_clause,[],[f851])).
% 0.22/0.59  fof(f232,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f229])).
% 0.22/0.59  fof(f229,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(superposition,[],[f63,f71])).
% 0.22/0.59  fof(f71,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f23])).
% 0.22/0.59  fof(f23,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.59  fof(f856,plain,(
% 0.22/0.59    spl3_56 | ~spl3_39 | ~spl3_54),
% 0.22/0.59    inference(avatar_split_clause,[],[f855,f778,f453,f851])).
% 0.22/0.59  fof(f453,plain,(
% 0.22/0.59    spl3_39 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.59  fof(f778,plain,(
% 0.22/0.59    spl3_54 <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.22/0.59  fof(f855,plain,(
% 0.22/0.59    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_39 | ~spl3_54)),
% 0.22/0.59    inference(subsumption_resolution,[],[f847,f454])).
% 0.22/0.59  fof(f454,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_39),
% 0.22/0.59    inference(avatar_component_clause,[],[f453])).
% 0.22/0.59  fof(f847,plain,(
% 0.22/0.59    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_54),
% 0.22/0.59    inference(superposition,[],[f63,f780])).
% 0.22/0.59  fof(f780,plain,(
% 0.22/0.59    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~spl3_54),
% 0.22/0.59    inference(avatar_component_clause,[],[f778])).
% 0.22/0.59  fof(f781,plain,(
% 0.22/0.59    spl3_53 | spl3_54 | ~spl3_40 | ~spl3_50),
% 0.22/0.59    inference(avatar_split_clause,[],[f773,f709,f457,f778,f775])).
% 0.22/0.59  fof(f457,plain,(
% 0.22/0.59    spl3_40 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.59  fof(f709,plain,(
% 0.22/0.59    spl3_50 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.59  fof(f773,plain,(
% 0.22/0.59    ( ! [X2] : (sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_40 | ~spl3_50)),
% 0.22/0.59    inference(subsumption_resolution,[],[f755,f459])).
% 0.22/0.59  fof(f459,plain,(
% 0.22/0.59    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_40),
% 0.22/0.59    inference(avatar_component_clause,[],[f457])).
% 0.22/0.59  fof(f755,plain,(
% 0.22/0.59    ( ! [X2] : (sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_50),
% 0.22/0.59    inference(superposition,[],[f265,f711])).
% 0.22/0.59  fof(f711,plain,(
% 0.22/0.59    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_50),
% 0.22/0.59    inference(avatar_component_clause,[],[f709])).
% 0.22/0.59  fof(f265,plain,(
% 0.22/0.59    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f261,f80])).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f42])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.59  fof(f261,plain,(
% 0.22/0.59    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 0.22/0.59    inference(superposition,[],[f73,f87])).
% 0.22/0.59  fof(f87,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f47])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.22/0.59  fof(f73,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.22/0.59  fof(f713,plain,(
% 0.22/0.59    spl3_41 | ~spl3_47),
% 0.22/0.59    inference(avatar_split_clause,[],[f700,f551,f463])).
% 0.22/0.59  fof(f463,plain,(
% 0.22/0.59    spl3_41 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.59  fof(f551,plain,(
% 0.22/0.59    spl3_47 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.22/0.59  fof(f700,plain,(
% 0.22/0.59    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_47),
% 0.22/0.59    inference(superposition,[],[f142,f553])).
% 0.22/0.59  fof(f553,plain,(
% 0.22/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_47),
% 0.22/0.59    inference(avatar_component_clause,[],[f551])).
% 0.22/0.59  fof(f142,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X1,k2_xboole_0(X1,X0))) )),
% 0.22/0.59    inference(superposition,[],[f138,f69])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.59  fof(f138,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.22/0.59    inference(resolution,[],[f83,f85])).
% 0.22/0.59  fof(f85,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.59    inference(ennf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.59  fof(f712,plain,(
% 0.22/0.59    ~spl3_39 | spl3_50 | ~spl3_13),
% 0.22/0.59    inference(avatar_split_clause,[],[f481,f199,f709,f453])).
% 0.22/0.59  fof(f199,plain,(
% 0.22/0.59    spl3_13 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.59  fof(f481,plain,(
% 0.22/0.59    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_13),
% 0.22/0.59    inference(superposition,[],[f154,f201])).
% 0.22/0.59  fof(f201,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_13),
% 0.22/0.59    inference(avatar_component_clause,[],[f199])).
% 0.22/0.59  fof(f154,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f150])).
% 0.22/0.59  fof(f150,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(superposition,[],[f67,f68])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.59  fof(f696,plain,(
% 0.22/0.59    spl3_47 | ~spl3_36 | ~spl3_46),
% 0.22/0.59    inference(avatar_split_clause,[],[f695,f547,f428,f551])).
% 0.22/0.59  fof(f428,plain,(
% 0.22/0.59    spl3_36 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.59  fof(f547,plain,(
% 0.22/0.59    spl3_46 <=> r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.22/0.59  fof(f695,plain,(
% 0.22/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_36 | ~spl3_46)),
% 0.22/0.59    inference(subsumption_resolution,[],[f693,f430])).
% 0.22/0.59  fof(f430,plain,(
% 0.22/0.59    r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_36),
% 0.22/0.59    inference(avatar_component_clause,[],[f428])).
% 0.22/0.59  fof(f693,plain,(
% 0.22/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_46),
% 0.22/0.59    inference(resolution,[],[f548,f66])).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f54])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(flattening,[],[f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.59    inference(nnf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.59  fof(f548,plain,(
% 0.22/0.59    r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~spl3_46),
% 0.22/0.59    inference(avatar_component_clause,[],[f547])).
% 0.22/0.59  fof(f692,plain,(
% 0.22/0.59    ~spl3_3 | ~spl3_4 | spl3_46),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f691])).
% 0.22/0.59  fof(f691,plain,(
% 0.22/0.59    $false | (~spl3_3 | ~spl3_4 | spl3_46)),
% 0.22/0.59    inference(subsumption_resolution,[],[f690,f109])).
% 0.22/0.59  fof(f690,plain,(
% 0.22/0.59    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_46)),
% 0.22/0.59    inference(subsumption_resolution,[],[f689,f104])).
% 0.22/0.59  fof(f689,plain,(
% 0.22/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_46),
% 0.22/0.59    inference(subsumption_resolution,[],[f686,f89])).
% 0.22/0.59  fof(f89,plain,(
% 0.22/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.59    inference(equality_resolution,[],[f65])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f54])).
% 0.22/0.59  fof(f686,plain,(
% 0.22/0.59    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_46),
% 0.22/0.59    inference(superposition,[],[f549,f683])).
% 0.22/0.59  fof(f683,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f236,f272])).
% 0.22/0.59  fof(f272,plain,(
% 0.22/0.59    ( ! [X2,X3] : (m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f269,f74])).
% 0.22/0.59  fof(f74,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f36])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(flattening,[],[f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,axiom,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.59  fof(f269,plain,(
% 0.22/0.59    ( ! [X2,X3] : (m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.22/0.59    inference(superposition,[],[f72,f70])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.22/0.59  fof(f72,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.22/0.59  fof(f236,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f235])).
% 0.22/0.59  fof(f235,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(superposition,[],[f86,f75])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f46])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(flattening,[],[f45])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.59    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.59  fof(f549,plain,(
% 0.22/0.59    ~r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) | spl3_46),
% 0.22/0.59    inference(avatar_component_clause,[],[f547])).
% 0.22/0.59  fof(f466,plain,(
% 0.22/0.59    ~spl3_41 | spl3_39),
% 0.22/0.59    inference(avatar_split_clause,[],[f461,f453,f463])).
% 0.22/0.59  fof(f461,plain,(
% 0.22/0.59    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_39),
% 0.22/0.59    inference(resolution,[],[f455,f79])).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f55])).
% 0.22/0.59  fof(f55,plain,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.59    inference(nnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.59  fof(f455,plain,(
% 0.22/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_39),
% 0.22/0.59    inference(avatar_component_clause,[],[f453])).
% 0.22/0.59  fof(f460,plain,(
% 0.22/0.59    ~spl3_39 | spl3_40 | ~spl3_13),
% 0.22/0.59    inference(avatar_split_clause,[],[f451,f199,f457,f453])).
% 0.22/0.59  fof(f451,plain,(
% 0.22/0.59    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_13),
% 0.22/0.59    inference(superposition,[],[f153,f201])).
% 0.22/0.59  fof(f153,plain,(
% 0.22/0.59    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f151])).
% 0.22/0.59  fof(f151,plain,(
% 0.22/0.59    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 0.22/0.59    inference(superposition,[],[f80,f68])).
% 0.22/0.59  fof(f431,plain,(
% 0.22/0.59    spl3_36 | ~spl3_13),
% 0.22/0.59    inference(avatar_split_clause,[],[f426,f199,f428])).
% 0.22/0.59  fof(f426,plain,(
% 0.22/0.59    r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_13),
% 0.22/0.59    inference(superposition,[],[f139,f201])).
% 0.22/0.59  fof(f139,plain,(
% 0.22/0.59    ( ! [X2,X3] : (r1_tarski(X2,k2_xboole_0(X3,k4_xboole_0(X2,X3)))) )),
% 0.22/0.59    inference(resolution,[],[f83,f89])).
% 0.22/0.59  fof(f372,plain,(
% 0.22/0.59    ~spl3_14 | spl3_15 | ~spl3_12),
% 0.22/0.59    inference(avatar_split_clause,[],[f371,f185,f210,f206])).
% 0.22/0.59  fof(f206,plain,(
% 0.22/0.59    spl3_14 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.59  fof(f185,plain,(
% 0.22/0.59    spl3_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.59  fof(f371,plain,(
% 0.22/0.59    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_12),
% 0.22/0.59    inference(resolution,[],[f187,f66])).
% 0.22/0.59  fof(f187,plain,(
% 0.22/0.59    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_12),
% 0.22/0.59    inference(avatar_component_clause,[],[f185])).
% 0.22/0.59  fof(f370,plain,(
% 0.22/0.59    spl3_13 | ~spl3_2 | ~spl3_9),
% 0.22/0.59    inference(avatar_split_clause,[],[f369,f160,f96,f199])).
% 0.22/0.59  fof(f96,plain,(
% 0.22/0.59    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.59  fof(f160,plain,(
% 0.22/0.59    spl3_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.59  fof(f369,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_9)),
% 0.22/0.59    inference(subsumption_resolution,[],[f365,f161])).
% 0.22/0.59  fof(f161,plain,(
% 0.22/0.59    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 0.22/0.59    inference(avatar_component_clause,[],[f160])).
% 0.22/0.59  fof(f365,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.22/0.59    inference(superposition,[],[f63,f97])).
% 0.22/0.59  fof(f97,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f96])).
% 0.22/0.59  fof(f363,plain,(
% 0.22/0.59    spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_15),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f362])).
% 0.22/0.59  fof(f362,plain,(
% 0.22/0.59    $false | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_15)),
% 0.22/0.59    inference(subsumption_resolution,[],[f361,f109])).
% 0.22/0.59  fof(f361,plain,(
% 0.22/0.59    ~l1_pre_topc(sK0) | (spl3_2 | ~spl3_3 | ~spl3_15)),
% 0.22/0.59    inference(subsumption_resolution,[],[f360,f104])).
% 0.22/0.59  fof(f360,plain,(
% 0.22/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_2 | ~spl3_15)),
% 0.22/0.59    inference(subsumption_resolution,[],[f359,f98])).
% 0.22/0.59  fof(f98,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f96])).
% 0.22/0.59  fof(f359,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_15),
% 0.22/0.59    inference(superposition,[],[f70,f212])).
% 0.22/0.59  fof(f212,plain,(
% 0.22/0.59    sK1 = k1_tops_1(sK0,sK1) | ~spl3_15),
% 0.22/0.59    inference(avatar_component_clause,[],[f210])).
% 0.22/0.59  fof(f317,plain,(
% 0.22/0.59    ~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_14),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f316])).
% 0.22/0.59  fof(f316,plain,(
% 0.22/0.59    $false | (~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_14)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f109,f89,f208,f104,f104,f93,f77])).
% 0.22/0.59  fof(f77,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(flattening,[],[f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.22/0.59  fof(f93,plain,(
% 0.22/0.59    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f92])).
% 0.22/0.59  fof(f92,plain,(
% 0.22/0.59    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.59  fof(f208,plain,(
% 0.22/0.59    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl3_14),
% 0.22/0.59    inference(avatar_component_clause,[],[f206])).
% 0.22/0.59  fof(f227,plain,(
% 0.22/0.59    spl3_16 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.22/0.59    inference(avatar_split_clause,[],[f222,f112,f107,f102,f224])).
% 0.22/0.59  fof(f224,plain,(
% 0.22/0.59    spl3_16 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.59  fof(f112,plain,(
% 0.22/0.59    spl3_5 <=> v2_pre_topc(sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.59  fof(f222,plain,(
% 0.22/0.59    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.22/0.59    inference(subsumption_resolution,[],[f221,f114])).
% 0.22/0.59  fof(f114,plain,(
% 0.22/0.59    v2_pre_topc(sK0) | ~spl3_5),
% 0.22/0.59    inference(avatar_component_clause,[],[f112])).
% 0.22/0.59  fof(f221,plain,(
% 0.22/0.59    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 0.22/0.59    inference(subsumption_resolution,[],[f218,f109])).
% 0.22/0.59  fof(f218,plain,(
% 0.22/0.59    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 0.22/0.59    inference(resolution,[],[f76,f104])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.59    inference(flattening,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,axiom,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.22/0.59  fof(f197,plain,(
% 0.22/0.59    ~spl3_3 | ~spl3_4 | spl3_9),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f196])).
% 0.22/0.59  fof(f196,plain,(
% 0.22/0.59    $false | (~spl3_3 | ~spl3_4 | spl3_9)),
% 0.22/0.59    inference(subsumption_resolution,[],[f195,f109])).
% 0.22/0.59  fof(f195,plain,(
% 0.22/0.59    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_9)),
% 0.22/0.59    inference(subsumption_resolution,[],[f190,f104])).
% 0.22/0.59  fof(f190,plain,(
% 0.22/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 0.22/0.59    inference(resolution,[],[f74,f162])).
% 0.22/0.59  fof(f162,plain,(
% 0.22/0.59    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 0.22/0.59    inference(avatar_component_clause,[],[f160])).
% 0.22/0.59  fof(f188,plain,(
% 0.22/0.59    spl3_12 | ~spl3_3 | ~spl3_4),
% 0.22/0.59    inference(avatar_split_clause,[],[f183,f107,f102,f185])).
% 0.22/0.59  fof(f183,plain,(
% 0.22/0.59    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 0.22/0.59    inference(subsumption_resolution,[],[f181,f109])).
% 0.22/0.59  fof(f181,plain,(
% 0.22/0.59    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 0.22/0.59    inference(resolution,[],[f82,f104])).
% 0.22/0.59  fof(f82,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.59  fof(f115,plain,(
% 0.22/0.59    spl3_5),
% 0.22/0.59    inference(avatar_split_clause,[],[f58,f112])).
% 0.22/0.59  fof(f58,plain,(
% 0.22/0.59    v2_pre_topc(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.59    inference(flattening,[],[f48])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.59    inference(nnf_transformation,[],[f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.59    inference(flattening,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f25])).
% 0.22/0.59  fof(f25,negated_conjecture,(
% 0.22/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.22/0.59    inference(negated_conjecture,[],[f24])).
% 0.22/0.59  fof(f24,conjecture,(
% 0.22/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 0.22/0.59  fof(f110,plain,(
% 0.22/0.59    spl3_4),
% 0.22/0.59    inference(avatar_split_clause,[],[f59,f107])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    l1_pre_topc(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  fof(f105,plain,(
% 0.22/0.59    spl3_3),
% 0.22/0.59    inference(avatar_split_clause,[],[f60,f102])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  fof(f100,plain,(
% 0.22/0.59    spl3_1 | spl3_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f61,f96,f92])).
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  fof(f99,plain,(
% 0.22/0.59    ~spl3_1 | ~spl3_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f62,f96,f92])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (19990)------------------------------
% 0.22/0.59  % (19990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (19990)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (19990)Memory used [KB]: 6908
% 0.22/0.59  % (19990)Time elapsed: 0.158 s
% 0.22/0.59  % (19990)------------------------------
% 0.22/0.59  % (19990)------------------------------
% 0.22/0.59  % (19964)Success in time 0.219 s
%------------------------------------------------------------------------------
