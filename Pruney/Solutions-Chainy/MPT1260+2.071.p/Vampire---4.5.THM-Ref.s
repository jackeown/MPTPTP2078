%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:45 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 313 expanded)
%              Number of leaves         :   36 ( 104 expanded)
%              Depth                    :   15
%              Number of atoms          :  430 ( 881 expanded)
%              Number of equality atoms :   62 ( 173 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f664,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f87,f125,f139,f164,f166,f278,f393,f473,f558,f578,f586,f591,f614,f620,f650,f653,f655,f657,f663])).

fof(f663,plain,(
    spl3_46 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | spl3_46 ),
    inference(unit_resulting_resolution,[],[f342,f570,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f570,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_46 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl3_46
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f342,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f335,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f335,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f326,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f326,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(k3_subset_1(X7,X6),k1_zfmisc_1(X7))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | m1_subset_1(X6,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f55,f318])).

fof(f318,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X1,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f317])).

fof(f317,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X1,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f75,f314])).

fof(f314,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,X1,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,X1,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f246,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f246,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X1,X0) = k7_subset_1(X1,k3_subset_1(X1,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ) ),
    inference(condensation,[],[f245])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f70,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f55,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f657,plain,
    ( ~ spl3_6
    | ~ spl3_15
    | spl3_14 ),
    inference(avatar_split_clause,[],[f624,f226,f230,f122])).

fof(f122,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f230,plain,
    ( spl3_15
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f226,plain,
    ( spl3_14
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f624,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f206])).

fof(f206,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | k1_tops_1(X3,X2) = X2
      | ~ r1_tarski(X2,k1_tops_1(X3,X2))
      | ~ l1_pre_topc(X3) ) ),
    inference(superposition,[],[f93,f202])).

fof(f202,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f75,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f93,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k6_subset_1(X1,X2))
      | k6_subset_1(X1,X2) = X1 ) ),
    inference(resolution,[],[f67,f89])).

fof(f89,plain,(
    ! [X2,X3] : r1_tarski(k6_subset_1(X2,X3),X2) ),
    inference(resolution,[],[f69,f55])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f655,plain,
    ( ~ spl3_1
    | ~ spl3_46
    | spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f621,f276,f230,f568,f79])).

fof(f79,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f276,plain,
    ( spl3_16
  <=> ! [X19] :
        ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X19,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X19,sK1)
        | ~ v3_pre_topc(X19,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f621,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_16 ),
    inference(resolution,[],[f46,f277])).

fof(f277,plain,
    ( ! [X19] :
        ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X19,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X19,sK1)
        | ~ v3_pre_topc(X19,sK0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f276])).

fof(f653,plain,
    ( ~ spl3_6
    | ~ spl3_47
    | spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f635,f226,f83,f601,f122])).

fof(f601,plain,
    ( spl3_47
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f83,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f635,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_14 ),
    inference(superposition,[],[f52,f228])).

fof(f228,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f226])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f650,plain,
    ( spl3_1
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f649])).

fof(f649,plain,
    ( $false
    | spl3_1
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f81,f634])).

fof(f634,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(superposition,[],[f159,f228])).

fof(f159,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_11
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f81,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f620,plain,(
    spl3_47 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | spl3_47 ),
    inference(subsumption_resolution,[],[f46,f603])).

fof(f603,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f601])).

fof(f614,plain,
    ( ~ spl3_6
    | ~ spl3_47
    | spl3_14
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f594,f555,f226,f601,f122])).

fof(f555,plain,
    ( spl3_43
  <=> sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f594,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_43 ),
    inference(superposition,[],[f202,f557])).

fof(f557,plain,
    ( sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f555])).

fof(f591,plain,
    ( ~ spl3_8
    | spl3_40 ),
    inference(avatar_contradiction_clause,[],[f587])).

fof(f587,plain,
    ( $false
    | ~ spl3_8
    | spl3_40 ),
    inference(subsumption_resolution,[],[f574,f583])).

fof(f583,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f89,f135])).

fof(f135,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_8
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f574,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | spl3_40 ),
    inference(resolution,[],[f543,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f543,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_40 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl3_40
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f586,plain,
    ( ~ spl3_30
    | spl3_31
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f581,f133,f457,f453])).

fof(f453,plain,
    ( spl3_30
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f457,plain,
    ( spl3_31
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f581,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_8 ),
    inference(superposition,[],[f74,f135])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f578,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f576,f83,f133,f129])).

fof(f129,plain,
    ( spl3_7
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f576,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f75,f84])).

fof(f84,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f558,plain,
    ( ~ spl3_40
    | ~ spl3_30
    | spl3_43
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f528,f457,f555,f453,f541])).

fof(f528,plain,
    ( sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_31 ),
    inference(superposition,[],[f318,f459])).

fof(f459,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f457])).

fof(f473,plain,
    ( ~ spl3_5
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | ~ spl3_5
    | spl3_30 ),
    inference(unit_resulting_resolution,[],[f120,f455,f68])).

fof(f455,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f453])).

fof(f120,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_5
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f393,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f48,f46,f131,f373])).

fof(f373,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f371])).

fof(f371,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f183,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

% (3180)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f72,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f131,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f278,plain,
    ( ~ spl3_6
    | spl3_16 ),
    inference(avatar_split_clause,[],[f272,f276,f122])).

fof(f272,plain,(
    ! [X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v3_pre_topc(X19,sK0)
      | ~ r1_tarski(X19,sK1)
      | r1_tarski(X19,k1_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f53,f46])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f166,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | spl3_12 ),
    inference(subsumption_resolution,[],[f47,f163])).

fof(f163,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f164,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f154,f122,f161,f157])).

fof(f154,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f139,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f48,f124])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f125,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f115,f122,f118])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f49,f46])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f87,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f44,f83,f79])).

fof(f44,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f45,f83,f79])).

fof(f45,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:48:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.48  % (3163)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.49  % (3166)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.49  % (3158)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.50  % (3160)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.50  % (3161)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.50  % (3175)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.50  % (3162)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (3179)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.50  % (3171)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.51  % (3183)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (3178)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.52  % (3170)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.52  % (3168)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.52  % (3159)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.53  % (3157)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.53  % (3165)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.53  % (3184)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.53  % (3181)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.53  % (3185)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.54  % (3185)Refutation not found, incomplete strategy% (3185)------------------------------
% 0.19/0.54  % (3185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (3185)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (3185)Memory used [KB]: 10874
% 0.19/0.54  % (3185)Time elapsed: 0.140 s
% 0.19/0.54  % (3185)------------------------------
% 0.19/0.54  % (3185)------------------------------
% 0.19/0.54  % (3176)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.54  % (3173)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.54  % (3177)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.54  % (3173)Refutation not found, incomplete strategy% (3173)------------------------------
% 0.19/0.54  % (3173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (3173)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (3173)Memory used [KB]: 10746
% 0.19/0.54  % (3173)Time elapsed: 0.140 s
% 0.19/0.54  % (3173)------------------------------
% 0.19/0.54  % (3173)------------------------------
% 0.19/0.54  % (3186)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.54  % (3167)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.44/0.55  % (3169)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.44/0.55  % (3167)Refutation not found, incomplete strategy% (3167)------------------------------
% 1.44/0.55  % (3167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (3167)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (3167)Memory used [KB]: 10874
% 1.44/0.55  % (3167)Time elapsed: 0.154 s
% 1.44/0.55  % (3167)------------------------------
% 1.44/0.55  % (3167)------------------------------
% 1.44/0.55  % (3174)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.55  % (3170)Refutation found. Thanks to Tanya!
% 1.44/0.55  % SZS status Theorem for theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  fof(f664,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(avatar_sat_refutation,[],[f86,f87,f125,f139,f164,f166,f278,f393,f473,f558,f578,f586,f591,f614,f620,f650,f653,f655,f657,f663])).
% 1.44/0.55  fof(f663,plain,(
% 1.44/0.55    spl3_46),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f659])).
% 1.44/0.55  fof(f659,plain,(
% 1.44/0.55    $false | spl3_46),
% 1.44/0.55    inference(unit_resulting_resolution,[],[f342,f570,f69])).
% 1.44/0.55  fof(f69,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f14])).
% 1.44/0.55  fof(f14,axiom,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.44/0.55  fof(f570,plain,(
% 1.44/0.55    ~r1_tarski(sK1,sK1) | spl3_46),
% 1.44/0.55    inference(avatar_component_clause,[],[f568])).
% 1.44/0.55  fof(f568,plain,(
% 1.44/0.55    spl3_46 <=> r1_tarski(sK1,sK1)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.44/0.55  fof(f342,plain,(
% 1.44/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.44/0.55    inference(resolution,[],[f335,f46])).
% 1.44/0.55  fof(f46,plain,(
% 1.44/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.55    inference(cnf_transformation,[],[f25])).
% 1.44/0.55  fof(f25,plain,(
% 1.44/0.55    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.44/0.55    inference(flattening,[],[f24])).
% 1.44/0.55  fof(f24,plain,(
% 1.44/0.55    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f23])).
% 1.44/0.55  fof(f23,negated_conjecture,(
% 1.44/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.44/0.55    inference(negated_conjecture,[],[f22])).
% 1.44/0.55  fof(f22,conjecture,(
% 1.44/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 1.44/0.55  fof(f335,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(duplicate_literal_removal,[],[f331])).
% 1.44/0.55  fof(f331,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.44/0.55    inference(resolution,[],[f326,f59])).
% 1.44/0.55  fof(f59,plain,(
% 1.44/0.55    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f32])).
% 1.44/0.55  fof(f32,plain,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.44/0.55  fof(f326,plain,(
% 1.44/0.55    ( ! [X6,X7] : (~m1_subset_1(k3_subset_1(X7,X6),k1_zfmisc_1(X7)) | ~m1_subset_1(X6,k1_zfmisc_1(X7)) | m1_subset_1(X6,k1_zfmisc_1(X6))) )),
% 1.44/0.55    inference(superposition,[],[f55,f318])).
% 1.44/0.55  fof(f318,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k6_subset_1(X1,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(duplicate_literal_removal,[],[f317])).
% 1.44/0.55  fof(f317,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k6_subset_1(X1,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(superposition,[],[f75,f314])).
% 1.44/0.55  fof(f314,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k7_subset_1(X0,X1,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(duplicate_literal_removal,[],[f309])).
% 1.44/0.55  fof(f309,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k7_subset_1(X0,X1,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(superposition,[],[f246,f61])).
% 1.44/0.55  fof(f61,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f34])).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f9])).
% 1.44/0.55  fof(f9,axiom,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.44/0.55  fof(f246,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k3_subset_1(X1,X0) = k7_subset_1(X1,k3_subset_1(X1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1))) )),
% 1.44/0.55    inference(condensation,[],[f245])).
% 1.44/0.55  fof(f245,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(superposition,[],[f70,f62])).
% 1.44/0.55  fof(f62,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f35])).
% 1.44/0.55  fof(f35,plain,(
% 1.44/0.55    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f12])).
% 1.44/0.55  fof(f12,axiom,(
% 1.44/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 1.44/0.55  fof(f70,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f40])).
% 1.44/0.55  fof(f40,plain,(
% 1.44/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f8])).
% 1.44/0.55  fof(f8,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 1.44/0.55  fof(f75,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(definition_unfolding,[],[f71,f56])).
% 1.44/0.55  fof(f56,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f10])).
% 1.44/0.55  fof(f10,axiom,(
% 1.44/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.44/0.55  fof(f71,plain,(
% 1.44/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f41])).
% 1.44/0.55  fof(f41,plain,(
% 1.44/0.55    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.55    inference(ennf_transformation,[],[f11])).
% 1.44/0.55  fof(f11,axiom,(
% 1.44/0.55    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.44/0.55  fof(f55,plain,(
% 1.44/0.55    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.44/0.55    inference(cnf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.44/0.55  fof(f657,plain,(
% 1.44/0.55    ~spl3_6 | ~spl3_15 | spl3_14),
% 1.44/0.55    inference(avatar_split_clause,[],[f624,f226,f230,f122])).
% 1.44/0.55  fof(f122,plain,(
% 1.44/0.55    spl3_6 <=> l1_pre_topc(sK0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.44/0.55  fof(f230,plain,(
% 1.44/0.55    spl3_15 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.44/0.55  fof(f226,plain,(
% 1.44/0.55    spl3_14 <=> sK1 = k1_tops_1(sK0,sK1)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.44/0.55  fof(f624,plain,(
% 1.44/0.55    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.44/0.55    inference(resolution,[],[f46,f206])).
% 1.44/0.55  fof(f206,plain,(
% 1.44/0.55    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | k1_tops_1(X3,X2) = X2 | ~r1_tarski(X2,k1_tops_1(X3,X2)) | ~l1_pre_topc(X3)) )),
% 1.44/0.55    inference(superposition,[],[f93,f202])).
% 1.44/0.55  fof(f202,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(duplicate_literal_removal,[],[f201])).
% 1.44/0.55  fof(f201,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k6_subset_1(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(superposition,[],[f75,f51])).
% 1.44/0.55  fof(f51,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f28])).
% 1.44/0.55  fof(f28,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f21])).
% 1.44/0.55  fof(f21,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 1.44/0.55  fof(f93,plain,(
% 1.44/0.55    ( ! [X2,X1] : (~r1_tarski(X1,k6_subset_1(X1,X2)) | k6_subset_1(X1,X2) = X1) )),
% 1.44/0.55    inference(resolution,[],[f67,f89])).
% 1.44/0.55  fof(f89,plain,(
% 1.44/0.55    ( ! [X2,X3] : (r1_tarski(k6_subset_1(X2,X3),X2)) )),
% 1.44/0.55    inference(resolution,[],[f69,f55])).
% 1.44/0.55  fof(f67,plain,(
% 1.44/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f1])).
% 1.44/0.55  fof(f1,axiom,(
% 1.44/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.55  fof(f655,plain,(
% 1.44/0.55    ~spl3_1 | ~spl3_46 | spl3_15 | ~spl3_16),
% 1.44/0.55    inference(avatar_split_clause,[],[f621,f276,f230,f568,f79])).
% 1.44/0.55  fof(f79,plain,(
% 1.44/0.55    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.44/0.55  fof(f276,plain,(
% 1.44/0.55    spl3_16 <=> ! [X19] : (~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X19,k1_tops_1(sK0,sK1)) | ~r1_tarski(X19,sK1) | ~v3_pre_topc(X19,sK0))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.44/0.55  fof(f621,plain,(
% 1.44/0.55    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0) | ~spl3_16),
% 1.44/0.55    inference(resolution,[],[f46,f277])).
% 1.44/0.55  fof(f277,plain,(
% 1.44/0.55    ( ! [X19] : (~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X19,k1_tops_1(sK0,sK1)) | ~r1_tarski(X19,sK1) | ~v3_pre_topc(X19,sK0)) ) | ~spl3_16),
% 1.44/0.55    inference(avatar_component_clause,[],[f276])).
% 1.44/0.55  fof(f653,plain,(
% 1.44/0.55    ~spl3_6 | ~spl3_47 | spl3_2 | ~spl3_14),
% 1.44/0.55    inference(avatar_split_clause,[],[f635,f226,f83,f601,f122])).
% 1.44/0.55  fof(f601,plain,(
% 1.44/0.55    spl3_47 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.44/0.55  fof(f83,plain,(
% 1.44/0.55    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.44/0.55  fof(f635,plain,(
% 1.44/0.55    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_14),
% 1.44/0.55    inference(superposition,[],[f52,f228])).
% 1.44/0.55  fof(f228,plain,(
% 1.44/0.55    sK1 = k1_tops_1(sK0,sK1) | ~spl3_14),
% 1.44/0.55    inference(avatar_component_clause,[],[f226])).
% 1.44/0.55  fof(f52,plain,(
% 1.44/0.55    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.55    inference(cnf_transformation,[],[f29])).
% 1.44/0.55  fof(f29,plain,(
% 1.44/0.55    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.55    inference(ennf_transformation,[],[f18])).
% 1.44/0.55  fof(f18,axiom,(
% 1.44/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.44/0.55  fof(f650,plain,(
% 1.44/0.55    spl3_1 | ~spl3_11 | ~spl3_14),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f649])).
% 1.44/0.55  fof(f649,plain,(
% 1.44/0.55    $false | (spl3_1 | ~spl3_11 | ~spl3_14)),
% 1.44/0.55    inference(subsumption_resolution,[],[f81,f634])).
% 1.44/0.55  fof(f634,plain,(
% 1.44/0.55    v3_pre_topc(sK1,sK0) | (~spl3_11 | ~spl3_14)),
% 1.44/0.55    inference(superposition,[],[f159,f228])).
% 1.44/0.55  fof(f159,plain,(
% 1.44/0.55    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl3_11),
% 1.44/0.55    inference(avatar_component_clause,[],[f157])).
% 1.44/0.55  fof(f157,plain,(
% 1.44/0.55    spl3_11 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.44/0.55  fof(f81,plain,(
% 1.44/0.55    ~v3_pre_topc(sK1,sK0) | spl3_1),
% 1.44/0.55    inference(avatar_component_clause,[],[f79])).
% 1.44/0.55  fof(f620,plain,(
% 1.44/0.55    spl3_47),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f616])).
% 1.44/0.55  fof(f616,plain,(
% 1.44/0.55    $false | spl3_47),
% 1.44/0.55    inference(subsumption_resolution,[],[f46,f603])).
% 1.44/0.55  fof(f603,plain,(
% 1.44/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_47),
% 1.44/0.55    inference(avatar_component_clause,[],[f601])).
% 1.44/0.55  fof(f614,plain,(
% 1.44/0.55    ~spl3_6 | ~spl3_47 | spl3_14 | ~spl3_43),
% 1.44/0.55    inference(avatar_split_clause,[],[f594,f555,f226,f601,f122])).
% 1.44/0.55  fof(f555,plain,(
% 1.44/0.55    spl3_43 <=> sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.44/0.55  fof(f594,plain,(
% 1.44/0.55    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_43),
% 1.44/0.55    inference(superposition,[],[f202,f557])).
% 1.44/0.55  fof(f557,plain,(
% 1.44/0.55    sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl3_43),
% 1.44/0.55    inference(avatar_component_clause,[],[f555])).
% 1.44/0.55  fof(f591,plain,(
% 1.44/0.55    ~spl3_8 | spl3_40),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f587])).
% 1.44/0.55  fof(f587,plain,(
% 1.44/0.55    $false | (~spl3_8 | spl3_40)),
% 1.44/0.55    inference(subsumption_resolution,[],[f574,f583])).
% 1.44/0.55  fof(f583,plain,(
% 1.44/0.55    r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl3_8),
% 1.44/0.55    inference(superposition,[],[f89,f135])).
% 1.44/0.55  fof(f135,plain,(
% 1.44/0.55    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl3_8),
% 1.44/0.55    inference(avatar_component_clause,[],[f133])).
% 1.44/0.55  fof(f133,plain,(
% 1.44/0.55    spl3_8 <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.44/0.55  fof(f574,plain,(
% 1.44/0.55    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | spl3_40),
% 1.44/0.56    inference(resolution,[],[f543,f68])).
% 1.44/0.56  fof(f68,plain,(
% 1.44/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f14])).
% 1.44/0.56  fof(f543,plain,(
% 1.44/0.56    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_40),
% 1.44/0.56    inference(avatar_component_clause,[],[f541])).
% 1.44/0.56  fof(f541,plain,(
% 1.44/0.56    spl3_40 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.44/0.56  fof(f586,plain,(
% 1.44/0.56    ~spl3_30 | spl3_31 | ~spl3_8),
% 1.44/0.56    inference(avatar_split_clause,[],[f581,f133,f457,f453])).
% 1.44/0.56  fof(f453,plain,(
% 1.44/0.56    spl3_30 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.44/0.56  fof(f457,plain,(
% 1.44/0.56    spl3_31 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.44/0.56  fof(f581,plain,(
% 1.44/0.56    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_8),
% 1.44/0.56    inference(superposition,[],[f74,f135])).
% 1.44/0.56  fof(f74,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k6_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.56    inference(definition_unfolding,[],[f60,f56])).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f33])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.44/0.56  fof(f578,plain,(
% 1.44/0.56    ~spl3_7 | spl3_8 | ~spl3_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f576,f83,f133,f129])).
% 1.44/0.56  fof(f129,plain,(
% 1.44/0.56    spl3_7 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.44/0.56  fof(f576,plain,(
% 1.44/0.56    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 1.44/0.56    inference(superposition,[],[f75,f84])).
% 1.44/0.56  fof(f84,plain,(
% 1.44/0.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f83])).
% 1.44/0.56  fof(f558,plain,(
% 1.44/0.56    ~spl3_40 | ~spl3_30 | spl3_43 | ~spl3_31),
% 1.44/0.56    inference(avatar_split_clause,[],[f528,f457,f555,f453,f541])).
% 1.44/0.56  fof(f528,plain,(
% 1.44/0.56    sK1 = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_31),
% 1.44/0.56    inference(superposition,[],[f318,f459])).
% 1.44/0.56  fof(f459,plain,(
% 1.44/0.56    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl3_31),
% 1.44/0.56    inference(avatar_component_clause,[],[f457])).
% 1.44/0.56  fof(f473,plain,(
% 1.44/0.56    ~spl3_5 | spl3_30),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f471])).
% 1.44/0.56  fof(f471,plain,(
% 1.44/0.56    $false | (~spl3_5 | spl3_30)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f120,f455,f68])).
% 1.44/0.56  fof(f455,plain,(
% 1.44/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_30),
% 1.44/0.56    inference(avatar_component_clause,[],[f453])).
% 1.44/0.56  fof(f120,plain,(
% 1.44/0.56    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_5),
% 1.44/0.56    inference(avatar_component_clause,[],[f118])).
% 1.44/0.56  fof(f118,plain,(
% 1.44/0.56    spl3_5 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.44/0.56  fof(f393,plain,(
% 1.44/0.56    spl3_7),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f377])).
% 1.44/0.56  fof(f377,plain,(
% 1.44/0.56    $false | spl3_7),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f48,f46,f131,f373])).
% 1.44/0.56  fof(f373,plain,(
% 1.44/0.56    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f371])).
% 1.44/0.56  fof(f371,plain,(
% 1.44/0.56    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.56    inference(resolution,[],[f183,f64])).
% 1.44/0.56  fof(f64,plain,(
% 1.44/0.56    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f39])).
% 1.44/0.56  % (3180)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.56  fof(f39,plain,(
% 1.44/0.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.56    inference(flattening,[],[f38])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,axiom,(
% 1.44/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.44/0.56  fof(f183,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f182])).
% 1.44/0.56  fof(f182,plain,(
% 1.44/0.56    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.56    inference(superposition,[],[f72,f50])).
% 1.44/0.56  fof(f50,plain,(
% 1.44/0.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f27])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f20])).
% 1.44/0.56  fof(f20,axiom,(
% 1.44/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 1.44/0.56  fof(f72,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f43])).
% 1.44/0.56  fof(f43,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.56    inference(flattening,[],[f42])).
% 1.44/0.56  fof(f42,plain,(
% 1.44/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.44/0.56    inference(ennf_transformation,[],[f5])).
% 1.44/0.56  fof(f5,axiom,(
% 1.44/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.44/0.56  fof(f131,plain,(
% 1.44/0.56    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_7),
% 1.44/0.56    inference(avatar_component_clause,[],[f129])).
% 1.44/0.56  fof(f48,plain,(
% 1.44/0.56    l1_pre_topc(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f278,plain,(
% 1.44/0.56    ~spl3_6 | spl3_16),
% 1.44/0.56    inference(avatar_split_clause,[],[f272,f276,f122])).
% 1.44/0.56  fof(f272,plain,(
% 1.44/0.56    ( ! [X19] : (~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_pre_topc(X19,sK0) | ~r1_tarski(X19,sK1) | r1_tarski(X19,k1_tops_1(sK0,sK1))) )),
% 1.44/0.56    inference(resolution,[],[f53,f46])).
% 1.44/0.56  fof(f53,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f31])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.56    inference(flattening,[],[f30])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f19])).
% 1.44/0.56  fof(f19,axiom,(
% 1.44/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 1.44/0.56  fof(f166,plain,(
% 1.44/0.56    spl3_12),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f165])).
% 1.44/0.56  fof(f165,plain,(
% 1.44/0.56    $false | spl3_12),
% 1.44/0.56    inference(subsumption_resolution,[],[f47,f163])).
% 1.44/0.56  fof(f163,plain,(
% 1.44/0.56    ~v2_pre_topc(sK0) | spl3_12),
% 1.44/0.56    inference(avatar_component_clause,[],[f161])).
% 1.44/0.56  fof(f161,plain,(
% 1.44/0.56    spl3_12 <=> v2_pre_topc(sK0)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.44/0.56  fof(f47,plain,(
% 1.44/0.56    v2_pre_topc(sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f164,plain,(
% 1.44/0.56    spl3_11 | ~spl3_12 | ~spl3_6),
% 1.44/0.56    inference(avatar_split_clause,[],[f154,f122,f161,f157])).
% 1.44/0.56  fof(f154,plain,(
% 1.44/0.56    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.44/0.56    inference(resolution,[],[f63,f46])).
% 1.44/0.56  fof(f63,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f37])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.44/0.56    inference(flattening,[],[f36])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f17])).
% 1.44/0.56  fof(f17,axiom,(
% 1.44/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.44/0.56  fof(f139,plain,(
% 1.44/0.56    spl3_6),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f138])).
% 1.44/0.56  fof(f138,plain,(
% 1.44/0.56    $false | spl3_6),
% 1.44/0.56    inference(subsumption_resolution,[],[f48,f124])).
% 1.44/0.56  fof(f124,plain,(
% 1.44/0.56    ~l1_pre_topc(sK0) | spl3_6),
% 1.44/0.56    inference(avatar_component_clause,[],[f122])).
% 1.44/0.56  fof(f125,plain,(
% 1.44/0.56    spl3_5 | ~spl3_6),
% 1.44/0.56    inference(avatar_split_clause,[],[f115,f122,f118])).
% 1.44/0.56  fof(f115,plain,(
% 1.44/0.56    ~l1_pre_topc(sK0) | r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.44/0.56    inference(resolution,[],[f49,f46])).
% 1.44/0.56  fof(f49,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 1.44/0.56    inference(cnf_transformation,[],[f26])).
% 1.44/0.56  fof(f26,plain,(
% 1.44/0.56    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.44/0.56    inference(ennf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,axiom,(
% 1.44/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.44/0.56  fof(f87,plain,(
% 1.44/0.56    spl3_1 | spl3_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f44,f83,f79])).
% 1.44/0.56  fof(f44,plain,(
% 1.44/0.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f86,plain,(
% 1.44/0.56    ~spl3_1 | ~spl3_2),
% 1.44/0.56    inference(avatar_split_clause,[],[f45,f83,f79])).
% 1.44/0.56  fof(f45,plain,(
% 1.44/0.56    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (3170)------------------------------
% 1.44/0.56  % (3170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (3170)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (3170)Memory used [KB]: 6652
% 1.44/0.56  % (3170)Time elapsed: 0.165 s
% 1.44/0.56  % (3170)------------------------------
% 1.44/0.56  % (3170)------------------------------
% 1.44/0.56  % (3172)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.61/0.56  % (3182)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.61/0.57  % (3164)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.61/0.58  % (3156)Success in time 0.225 s
%------------------------------------------------------------------------------
