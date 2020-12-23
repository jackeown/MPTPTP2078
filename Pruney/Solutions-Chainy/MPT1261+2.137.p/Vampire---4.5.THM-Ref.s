%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:09 EST 2020

% Result     : Theorem 6.97s
% Output     : Refutation 6.97s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 543 expanded)
%              Number of leaves         :   33 ( 186 expanded)
%              Depth                    :   13
%              Number of atoms          :  418 (1102 expanded)
%              Number of equality atoms :   95 ( 393 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12771,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f72,f188,f1574,f2332,f2334,f2431,f9179,f10542,f10660,f10824,f12338,f12351,f12372,f12424,f12619,f12654,f12658,f12770])).

fof(f12770,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f12764])).

fof(f12764,plain,
    ( $false
    | spl2_9 ),
    inference(unit_resulting_resolution,[],[f39,f37,f248,f627])).

fof(f627,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f626])).

fof(f626,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f57,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f248,plain,
    ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl2_9
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f12658,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f12656,f1564,f64,f1560])).

fof(f1560,plain,
    ( spl2_21
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f64,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1564,plain,
    ( spl2_22
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f12656,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f12654,plain,
    ( ~ spl2_21
    | spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f7983,f247,f182,f1560])).

fof(f182,plain,
    ( spl2_4
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f7983,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_9 ),
    inference(superposition,[],[f124,f249])).

fof(f249,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f247])).

fof(f124,plain,(
    ! [X6,X5] :
      ( k4_xboole_0(X6,k4_xboole_0(X6,X5)) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f48,f49,f49])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f12619,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f12618])).

fof(f12618,plain,
    ( $false
    | spl2_2
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f37,f12617])).

fof(f12617,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f12616])).

fof(f12616,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f12615,f184])).

fof(f184,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f182])).

fof(f12615,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f70,f57])).

fof(f70,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f12424,plain,
    ( ~ spl2_22
    | ~ spl2_3
    | ~ spl2_118
    | spl2_23
    | ~ spl2_172 ),
    inference(avatar_split_clause,[],[f12398,f12348,f1569,f9166,f178,f1564])).

fof(f178,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f9166,plain,
    ( spl2_118
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).

fof(f1569,plain,
    ( spl2_23
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f12348,plain,
    ( spl2_172
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_172])])).

fof(f12398,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_172 ),
    inference(superposition,[],[f745,f12350])).

fof(f12350,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_172 ),
    inference(avatar_component_clause,[],[f12348])).

fof(f745,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f744])).

fof(f744,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f58,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f12372,plain,(
    spl2_165 ),
    inference(avatar_contradiction_clause,[],[f12356])).

fof(f12356,plain,
    ( $false
    | spl2_165 ),
    inference(unit_resulting_resolution,[],[f61,f12282,f583])).

fof(f583,plain,(
    ! [X4,X3] :
      ( r1_tarski(X3,k2_xboole_0(X3,X4))
      | ~ r1_tarski(X3,X3) ) ),
    inference(superposition,[],[f506,f306])).

fof(f306,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k1_xboole_0) = X0
      | ~ r1_tarski(X0,X0) ) ),
    inference(condensation,[],[f293])).

fof(f293,plain,(
    ! [X8,X7] :
      ( k4_xboole_0(X7,k1_xboole_0) = X7
      | ~ r1_tarski(X7,X7)
      | ~ r1_tarski(X7,X8) ) ),
    inference(superposition,[],[f60,f270])).

fof(f270,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k4_xboole_0(X4,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f208,f60])).

fof(f208,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f190,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f190,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))) ),
    inference(superposition,[],[f157,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f157,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f132,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f51,f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f132,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(superposition,[],[f47,f59])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f506,plain,(
    ! [X28,X27] : r1_tarski(k4_xboole_0(X27,k1_xboole_0),k2_xboole_0(k4_xboole_0(X27,k1_xboole_0),X28)) ),
    inference(superposition,[],[f132,f211])).

fof(f211,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),X6)) ),
    inference(forward_demodulation,[],[f200,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f73,f47])).

fof(f200,plain,(
    ! [X6,X5] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),X6)) ),
    inference(superposition,[],[f56,f157])).

fof(f12282,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | spl2_165 ),
    inference(avatar_component_clause,[],[f12280])).

fof(f12280,plain,
    ( spl2_165
  <=> r1_tarski(sK1,k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_165])])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f12351,plain,
    ( spl2_172
    | ~ spl2_165
    | ~ spl2_163 ),
    inference(avatar_split_clause,[],[f12344,f12271,f12280,f12348])).

fof(f12271,plain,
    ( spl2_163
  <=> r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_163])])).

fof(f12344,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_163 ),
    inference(resolution,[],[f12272,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f12272,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1)
    | ~ spl2_163 ),
    inference(avatar_component_clause,[],[f12271])).

fof(f12338,plain,
    ( ~ spl2_22
    | ~ spl2_3
    | ~ spl2_118
    | ~ spl2_135
    | spl2_163 ),
    inference(avatar_split_clause,[],[f12336,f12271,f10608,f9166,f178,f1564])).

fof(f10608,plain,
    ( spl2_135
  <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).

fof(f12336,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_163 ),
    inference(superposition,[],[f12273,f745])).

fof(f12273,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1)
    | spl2_163 ),
    inference(avatar_component_clause,[],[f12271])).

fof(f10824,plain,(
    spl2_139 ),
    inference(avatar_contradiction_clause,[],[f10820])).

fof(f10820,plain,
    ( $false
    | spl2_139 ),
    inference(unit_resulting_resolution,[],[f61,f61,f10634,f2250])).

fof(f2250,plain,(
    ! [X50,X51,X49] :
      ( ~ r1_tarski(X50,X49)
      | ~ r1_tarski(X49,X51)
      | r1_tarski(X50,X51) ) ),
    inference(superposition,[],[f2206,f124])).

fof(f2206,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(k4_xboole_0(X5,X7),X6)
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f2089,f86])).

fof(f86,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(X2,X4)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f56,f60])).

fof(f2089,plain,(
    ! [X17,X15,X16] : r1_tarski(k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X15),X17)),X15) ),
    inference(forward_demodulation,[],[f1939,f56])).

fof(f1939,plain,(
    ! [X17,X15,X16] : r1_tarski(k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),X17),X15) ),
    inference(superposition,[],[f47,f133])).

fof(f133,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,X5),X6)) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6) ),
    inference(superposition,[],[f56,f59])).

fof(f10634,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | spl2_139 ),
    inference(avatar_component_clause,[],[f10632])).

fof(f10632,plain,
    ( spl2_139
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).

fof(f10660,plain,
    ( ~ spl2_139
    | spl2_135
    | ~ spl2_134 ),
    inference(avatar_split_clause,[],[f10648,f10539,f10608,f10632])).

fof(f10539,plain,
    ( spl2_134
  <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_134])])).

fof(f10648,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_134 ),
    inference(superposition,[],[f10572,f306])).

fof(f10572,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0),sK1)
    | ~ spl2_134 ),
    inference(superposition,[],[f132,f10545])).

fof(f10545,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_134 ),
    inference(resolution,[],[f10541,f4207])).

fof(f4207,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X3,X2),X2)
      | k1_xboole_0 = k4_xboole_0(X3,X2) ) ),
    inference(forward_demodulation,[],[f4125,f210])).

fof(f210,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f209,f40])).

fof(f209,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f194,f56])).

fof(f194,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0))) ),
    inference(superposition,[],[f157,f56])).

fof(f4125,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,X2) = k4_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X3,X2)))
      | ~ r1_tarski(k4_xboole_0(X3,X2),X2) ) ),
    inference(superposition,[],[f96,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f96,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))
      | ~ r1_tarski(k4_xboole_0(X3,X4),X5) ) ),
    inference(forward_demodulation,[],[f88,f56])).

fof(f88,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5)))
      | ~ r1_tarski(k4_xboole_0(X3,X4),X5) ) ),
    inference(superposition,[],[f56,f60])).

fof(f10541,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl2_134 ),
    inference(avatar_component_clause,[],[f10539])).

fof(f10542,plain,
    ( ~ spl2_22
    | ~ spl2_3
    | ~ spl2_118
    | spl2_134
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f10526,f182,f10539,f9166,f178,f1564])).

fof(f10526,plain,
    ( r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(superposition,[],[f6064,f745])).

fof(f6064,plain,
    ( ! [X18] : r1_tarski(k4_xboole_0(k2_xboole_0(X18,k2_tops_1(sK0,sK1)),X18),sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f6043,f5168])).

fof(f5168,plain,
    ( ! [X15] :
        ( ~ r1_tarski(X15,k2_tops_1(sK0,sK1))
        | r1_tarski(X15,sK1) )
    | ~ spl2_4 ),
    inference(superposition,[],[f4791,f184])).

fof(f4791,plain,(
    ! [X21,X22,X20] :
      ( ~ r1_tarski(X20,k4_xboole_0(X21,X22))
      | r1_tarski(X20,X21) ) ),
    inference(superposition,[],[f3600,f60])).

fof(f3600,plain,(
    ! [X28,X26,X27] : r1_tarski(k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X26,X27))),X26) ),
    inference(superposition,[],[f47,f152])).

fof(f152,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9)))) ),
    inference(forward_demodulation,[],[f125,f56])).

fof(f125,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(k4_xboole_0(X7,X8),X9))) ),
    inference(superposition,[],[f59,f56])).

fof(f6043,plain,(
    ! [X26,X27] : r1_tarski(k4_xboole_0(k2_xboole_0(X26,X27),X26),X27) ),
    inference(forward_demodulation,[],[f6007,f40])).

fof(f6007,plain,(
    ! [X26,X27] : r1_tarski(k4_xboole_0(k2_xboole_0(X26,X27),k2_xboole_0(X26,k1_xboole_0)),X27) ),
    inference(superposition,[],[f170,f748])).

fof(f748,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f716,f73])).

fof(f716,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) ),
    inference(resolution,[],[f204,f47])).

fof(f204,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(k4_xboole_0(X13,k1_xboole_0),X14)
      | r1_tarski(k4_xboole_0(X13,X14),k1_xboole_0) ) ),
    inference(superposition,[],[f102,f157])).

fof(f102,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k4_xboole_0(X6,X5),k4_xboole_0(X6,X4))
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f91,f51])).

fof(f91,plain,(
    ! [X6,X8,X7] : r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X8)),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f47,f56])).

fof(f170,plain,(
    ! [X8,X7,X9] : r1_tarski(k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9)))),X9) ),
    inference(forward_demodulation,[],[f163,f56])).

fof(f163,plain,(
    ! [X8,X7,X9] : r1_tarski(k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X9))),X9) ),
    inference(superposition,[],[f132,f56])).

fof(f9179,plain,(
    spl2_118 ),
    inference(avatar_contradiction_clause,[],[f9177])).

fof(f9177,plain,
    ( $false
    | spl2_118 ),
    inference(unit_resulting_resolution,[],[f39,f37,f9168,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f9168,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_118 ),
    inference(avatar_component_clause,[],[f9166])).

fof(f2431,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f2429,f68,f182,f178])).

fof(f2429,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f57,f69])).

fof(f69,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f2334,plain,(
    spl2_31 ),
    inference(avatar_contradiction_clause,[],[f2333])).

fof(f2333,plain,
    ( $false
    | spl2_31 ),
    inference(subsumption_resolution,[],[f38,f2331])).

fof(f2331,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_31 ),
    inference(avatar_component_clause,[],[f2329])).

fof(f2329,plain,
    ( spl2_31
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f2332,plain,
    ( spl2_1
    | ~ spl2_22
    | ~ spl2_31
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f1578,f1569,f178,f2329,f1564,f64])).

fof(f1578,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_23 ),
    inference(trivial_inequality_removal,[],[f1577])).

fof(f1577,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_23 ),
    inference(superposition,[],[f43,f1571])).

fof(f1571,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f1569])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f1574,plain,(
    spl2_22 ),
    inference(avatar_contradiction_clause,[],[f1573])).

fof(f1573,plain,
    ( $false
    | spl2_22 ),
    inference(subsumption_resolution,[],[f39,f1566])).

fof(f1566,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_22 ),
    inference(avatar_component_clause,[],[f1564])).

fof(f188,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f37,f180])).

fof(f180,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f178])).

fof(f72,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f35,f68,f64])).

fof(f35,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f36,f68,f64])).

fof(f36,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:29:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (17505)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (17503)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (17515)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (17510)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (17502)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (17523)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (17511)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (17519)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (17504)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (17506)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (17501)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (17517)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (17517)Refutation not found, incomplete strategy% (17517)------------------------------
% 0.22/0.54  % (17517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17530)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (17530)Refutation not found, incomplete strategy% (17530)------------------------------
% 0.22/0.54  % (17530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17530)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17530)Memory used [KB]: 1663
% 0.22/0.54  % (17530)Time elapsed: 0.130 s
% 0.22/0.54  % (17530)------------------------------
% 0.22/0.54  % (17530)------------------------------
% 0.22/0.54  % (17516)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (17517)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17517)Memory used [KB]: 10618
% 0.22/0.54  % (17517)Time elapsed: 0.125 s
% 0.22/0.54  % (17517)------------------------------
% 0.22/0.54  % (17517)------------------------------
% 0.22/0.55  % (17522)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (17527)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (17521)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (17528)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (17509)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (17511)Refutation not found, incomplete strategy% (17511)------------------------------
% 0.22/0.55  % (17511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17511)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17511)Memory used [KB]: 10746
% 0.22/0.55  % (17511)Time elapsed: 0.128 s
% 0.22/0.55  % (17511)------------------------------
% 0.22/0.55  % (17511)------------------------------
% 0.22/0.55  % (17507)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (17526)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (17525)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (17514)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (17512)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (17518)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (17529)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (17520)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (17524)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (17529)Refutation not found, incomplete strategy% (17529)------------------------------
% 0.22/0.56  % (17529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (17529)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (17529)Memory used [KB]: 10746
% 0.22/0.56  % (17529)Time elapsed: 0.140 s
% 0.22/0.56  % (17529)------------------------------
% 0.22/0.56  % (17529)------------------------------
% 0.22/0.56  % (17513)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (17508)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.23/0.69  % (17554)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.23/0.69  % (17552)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.23/0.70  % (17553)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.23/0.71  % (17555)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.20/0.82  % (17525)Time limit reached!
% 3.20/0.82  % (17525)------------------------------
% 3.20/0.82  % (17525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.82  % (17525)Termination reason: Time limit
% 3.20/0.82  
% 3.20/0.82  % (17525)Memory used [KB]: 14072
% 3.20/0.82  % (17525)Time elapsed: 0.402 s
% 3.20/0.82  % (17525)------------------------------
% 3.20/0.82  % (17525)------------------------------
% 3.20/0.82  % (17503)Time limit reached!
% 3.20/0.82  % (17503)------------------------------
% 3.20/0.82  % (17503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.82  % (17503)Termination reason: Time limit
% 3.20/0.82  % (17503)Termination phase: Saturation
% 3.20/0.82  
% 3.20/0.82  % (17503)Memory used [KB]: 6396
% 3.20/0.82  % (17503)Time elapsed: 0.400 s
% 3.20/0.82  % (17503)------------------------------
% 3.20/0.82  % (17503)------------------------------
% 4.27/0.92  % (17515)Time limit reached!
% 4.27/0.92  % (17515)------------------------------
% 4.27/0.92  % (17515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.92  % (17515)Termination reason: Time limit
% 4.27/0.92  % (17515)Termination phase: Saturation
% 4.27/0.92  
% 4.27/0.92  % (17515)Memory used [KB]: 6012
% 4.27/0.92  % (17515)Time elapsed: 0.500 s
% 4.27/0.92  % (17515)------------------------------
% 4.27/0.92  % (17515)------------------------------
% 4.27/0.94  % (17507)Time limit reached!
% 4.27/0.94  % (17507)------------------------------
% 4.27/0.94  % (17507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.94  % (17507)Termination reason: Time limit
% 4.27/0.94  
% 4.27/0.94  % (17507)Memory used [KB]: 14583
% 4.27/0.94  % (17507)Time elapsed: 0.515 s
% 4.27/0.94  % (17507)------------------------------
% 4.27/0.94  % (17507)------------------------------
% 4.53/0.96  % (17556)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.53/0.98  % (17557)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.08/1.06  % (17558)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.08/1.07  % (17559)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.47/1.11  % (17508)Time limit reached!
% 5.47/1.11  % (17508)------------------------------
% 5.47/1.11  % (17508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.47/1.11  % (17508)Termination reason: Time limit
% 5.47/1.11  
% 5.47/1.11  % (17508)Memory used [KB]: 7419
% 5.47/1.11  % (17508)Time elapsed: 0.625 s
% 5.47/1.11  % (17508)------------------------------
% 5.47/1.11  % (17508)------------------------------
% 6.50/1.22  % (17502)Time limit reached!
% 6.50/1.22  % (17502)------------------------------
% 6.50/1.22  % (17502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.50/1.22  % (17502)Termination reason: Time limit
% 6.50/1.22  % (17502)Termination phase: Saturation
% 6.50/1.22  
% 6.50/1.22  % (17502)Memory used [KB]: 8187
% 6.50/1.22  % (17502)Time elapsed: 0.800 s
% 6.50/1.22  % (17502)------------------------------
% 6.50/1.22  % (17502)------------------------------
% 6.97/1.25  % (17514)Refutation found. Thanks to Tanya!
% 6.97/1.25  % SZS status Theorem for theBenchmark
% 6.97/1.25  % SZS output start Proof for theBenchmark
% 6.97/1.25  fof(f12771,plain,(
% 6.97/1.25    $false),
% 6.97/1.25    inference(avatar_sat_refutation,[],[f71,f72,f188,f1574,f2332,f2334,f2431,f9179,f10542,f10660,f10824,f12338,f12351,f12372,f12424,f12619,f12654,f12658,f12770])).
% 6.97/1.25  fof(f12770,plain,(
% 6.97/1.25    spl2_9),
% 6.97/1.25    inference(avatar_contradiction_clause,[],[f12764])).
% 6.97/1.25  fof(f12764,plain,(
% 6.97/1.25    $false | spl2_9),
% 6.97/1.25    inference(unit_resulting_resolution,[],[f39,f37,f248,f627])).
% 6.97/1.26  fof(f627,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.97/1.26    inference(duplicate_literal_removal,[],[f626])).
% 6.97/1.26  fof(f626,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.97/1.26    inference(superposition,[],[f57,f41])).
% 6.97/1.26  fof(f41,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.97/1.26    inference(cnf_transformation,[],[f22])).
% 6.97/1.26  fof(f22,plain,(
% 6.97/1.26    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.97/1.26    inference(ennf_transformation,[],[f16])).
% 6.97/1.26  fof(f16,axiom,(
% 6.97/1.26    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 6.97/1.26  fof(f57,plain,(
% 6.97/1.26    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.97/1.26    inference(cnf_transformation,[],[f32])).
% 6.97/1.26  fof(f32,plain,(
% 6.97/1.26    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.97/1.26    inference(ennf_transformation,[],[f11])).
% 6.97/1.26  fof(f11,axiom,(
% 6.97/1.26    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 6.97/1.26  fof(f248,plain,(
% 6.97/1.26    k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_9),
% 6.97/1.26    inference(avatar_component_clause,[],[f247])).
% 6.97/1.26  fof(f247,plain,(
% 6.97/1.26    spl2_9 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 6.97/1.26  fof(f37,plain,(
% 6.97/1.26    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.97/1.26    inference(cnf_transformation,[],[f21])).
% 6.97/1.26  fof(f21,plain,(
% 6.97/1.26    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.97/1.26    inference(flattening,[],[f20])).
% 6.97/1.26  fof(f20,plain,(
% 6.97/1.26    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.97/1.26    inference(ennf_transformation,[],[f18])).
% 6.97/1.26  fof(f18,negated_conjecture,(
% 6.97/1.26    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 6.97/1.26    inference(negated_conjecture,[],[f17])).
% 6.97/1.26  fof(f17,conjecture,(
% 6.97/1.26    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 6.97/1.26  fof(f39,plain,(
% 6.97/1.26    l1_pre_topc(sK0)),
% 6.97/1.26    inference(cnf_transformation,[],[f21])).
% 6.97/1.26  fof(f12658,plain,(
% 6.97/1.26    spl2_21 | ~spl2_1 | ~spl2_22),
% 6.97/1.26    inference(avatar_split_clause,[],[f12656,f1564,f64,f1560])).
% 6.97/1.26  fof(f1560,plain,(
% 6.97/1.26    spl2_21 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 6.97/1.26  fof(f64,plain,(
% 6.97/1.26    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 6.97/1.26  fof(f1564,plain,(
% 6.97/1.26    spl2_22 <=> l1_pre_topc(sK0)),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 6.97/1.26  fof(f12656,plain,(
% 6.97/1.26    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 6.97/1.26    inference(resolution,[],[f37,f45])).
% 6.97/1.26  fof(f45,plain,(
% 6.97/1.26    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 6.97/1.26    inference(cnf_transformation,[],[f27])).
% 6.97/1.26  fof(f27,plain,(
% 6.97/1.26    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.97/1.26    inference(flattening,[],[f26])).
% 6.97/1.26  fof(f26,plain,(
% 6.97/1.26    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.97/1.26    inference(ennf_transformation,[],[f15])).
% 6.97/1.26  fof(f15,axiom,(
% 6.97/1.26    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 6.97/1.26  fof(f12654,plain,(
% 6.97/1.26    ~spl2_21 | spl2_4 | ~spl2_9),
% 6.97/1.26    inference(avatar_split_clause,[],[f7983,f247,f182,f1560])).
% 6.97/1.26  fof(f182,plain,(
% 6.97/1.26    spl2_4 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 6.97/1.26  fof(f7983,plain,(
% 6.97/1.26    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_9),
% 6.97/1.26    inference(superposition,[],[f124,f249])).
% 6.97/1.26  fof(f249,plain,(
% 6.97/1.26    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_9),
% 6.97/1.26    inference(avatar_component_clause,[],[f247])).
% 6.97/1.26  fof(f124,plain,(
% 6.97/1.26    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,X5)) = X5 | ~r1_tarski(X5,X6)) )),
% 6.97/1.26    inference(superposition,[],[f59,f60])).
% 6.97/1.26  fof(f60,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 6.97/1.26    inference(definition_unfolding,[],[f50,f49])).
% 6.97/1.26  fof(f49,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.97/1.26    inference(cnf_transformation,[],[f9])).
% 6.97/1.26  fof(f9,axiom,(
% 6.97/1.26    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.97/1.26  fof(f50,plain,(
% 6.97/1.26    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 6.97/1.26    inference(cnf_transformation,[],[f28])).
% 6.97/1.26  fof(f28,plain,(
% 6.97/1.26    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.97/1.26    inference(ennf_transformation,[],[f6])).
% 6.97/1.26  fof(f6,axiom,(
% 6.97/1.26    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.97/1.26  fof(f59,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 6.97/1.26    inference(definition_unfolding,[],[f48,f49,f49])).
% 6.97/1.26  fof(f48,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.97/1.26    inference(cnf_transformation,[],[f1])).
% 6.97/1.26  fof(f1,axiom,(
% 6.97/1.26    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.97/1.26  fof(f12619,plain,(
% 6.97/1.26    spl2_2 | ~spl2_4),
% 6.97/1.26    inference(avatar_contradiction_clause,[],[f12618])).
% 6.97/1.26  fof(f12618,plain,(
% 6.97/1.26    $false | (spl2_2 | ~spl2_4)),
% 6.97/1.26    inference(subsumption_resolution,[],[f37,f12617])).
% 6.97/1.26  fof(f12617,plain,(
% 6.97/1.26    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_2 | ~spl2_4)),
% 6.97/1.26    inference(trivial_inequality_removal,[],[f12616])).
% 6.97/1.26  fof(f12616,plain,(
% 6.97/1.26    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl2_2 | ~spl2_4)),
% 6.97/1.26    inference(forward_demodulation,[],[f12615,f184])).
% 6.97/1.26  fof(f184,plain,(
% 6.97/1.26    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_4),
% 6.97/1.26    inference(avatar_component_clause,[],[f182])).
% 6.97/1.26  fof(f12615,plain,(
% 6.97/1.26    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 6.97/1.26    inference(superposition,[],[f70,f57])).
% 6.97/1.26  fof(f70,plain,(
% 6.97/1.26    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 6.97/1.26    inference(avatar_component_clause,[],[f68])).
% 6.97/1.26  fof(f68,plain,(
% 6.97/1.26    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 6.97/1.26  fof(f12424,plain,(
% 6.97/1.26    ~spl2_22 | ~spl2_3 | ~spl2_118 | spl2_23 | ~spl2_172),
% 6.97/1.26    inference(avatar_split_clause,[],[f12398,f12348,f1569,f9166,f178,f1564])).
% 6.97/1.26  fof(f178,plain,(
% 6.97/1.26    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 6.97/1.26  fof(f9166,plain,(
% 6.97/1.26    spl2_118 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_118])])).
% 6.97/1.26  fof(f1569,plain,(
% 6.97/1.26    spl2_23 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 6.97/1.26  fof(f12348,plain,(
% 6.97/1.26    spl2_172 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_172])])).
% 6.97/1.26  fof(f12398,plain,(
% 6.97/1.26    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_172),
% 6.97/1.26    inference(superposition,[],[f745,f12350])).
% 6.97/1.26  fof(f12350,plain,(
% 6.97/1.26    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_172),
% 6.97/1.26    inference(avatar_component_clause,[],[f12348])).
% 6.97/1.26  fof(f745,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.97/1.26    inference(duplicate_literal_removal,[],[f744])).
% 6.97/1.26  fof(f744,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.97/1.26    inference(superposition,[],[f58,f42])).
% 6.97/1.26  fof(f42,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.97/1.26    inference(cnf_transformation,[],[f23])).
% 6.97/1.26  fof(f23,plain,(
% 6.97/1.26    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.97/1.26    inference(ennf_transformation,[],[f14])).
% 6.97/1.26  fof(f14,axiom,(
% 6.97/1.26    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 6.97/1.26  fof(f58,plain,(
% 6.97/1.26    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.97/1.26    inference(cnf_transformation,[],[f34])).
% 6.97/1.26  fof(f34,plain,(
% 6.97/1.26    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.97/1.26    inference(flattening,[],[f33])).
% 6.97/1.26  fof(f33,plain,(
% 6.97/1.26    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.97/1.26    inference(ennf_transformation,[],[f10])).
% 6.97/1.26  fof(f10,axiom,(
% 6.97/1.26    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 6.97/1.26  fof(f12372,plain,(
% 6.97/1.26    spl2_165),
% 6.97/1.26    inference(avatar_contradiction_clause,[],[f12356])).
% 6.97/1.26  fof(f12356,plain,(
% 6.97/1.26    $false | spl2_165),
% 6.97/1.26    inference(unit_resulting_resolution,[],[f61,f12282,f583])).
% 6.97/1.26  fof(f583,plain,(
% 6.97/1.26    ( ! [X4,X3] : (r1_tarski(X3,k2_xboole_0(X3,X4)) | ~r1_tarski(X3,X3)) )),
% 6.97/1.26    inference(superposition,[],[f506,f306])).
% 6.97/1.26  fof(f306,plain,(
% 6.97/1.26    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0 | ~r1_tarski(X0,X0)) )),
% 6.97/1.26    inference(condensation,[],[f293])).
% 6.97/1.26  fof(f293,plain,(
% 6.97/1.26    ( ! [X8,X7] : (k4_xboole_0(X7,k1_xboole_0) = X7 | ~r1_tarski(X7,X7) | ~r1_tarski(X7,X8)) )),
% 6.97/1.26    inference(superposition,[],[f60,f270])).
% 6.97/1.26  fof(f270,plain,(
% 6.97/1.26    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,X4) | ~r1_tarski(X4,X5)) )),
% 6.97/1.26    inference(superposition,[],[f208,f60])).
% 6.97/1.26  fof(f208,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 6.97/1.26    inference(forward_demodulation,[],[f190,f40])).
% 6.97/1.26  fof(f40,plain,(
% 6.97/1.26    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.97/1.26    inference(cnf_transformation,[],[f5])).
% 6.97/1.26  fof(f5,axiom,(
% 6.97/1.26    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 6.97/1.26  fof(f190,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)))) )),
% 6.97/1.26    inference(superposition,[],[f157,f56])).
% 6.97/1.26  fof(f56,plain,(
% 6.97/1.26    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 6.97/1.26    inference(cnf_transformation,[],[f8])).
% 6.97/1.26  fof(f8,axiom,(
% 6.97/1.26    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 6.97/1.26  fof(f157,plain,(
% 6.97/1.26    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 6.97/1.26    inference(resolution,[],[f132,f73])).
% 6.97/1.26  fof(f73,plain,(
% 6.97/1.26    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 6.97/1.26    inference(superposition,[],[f51,f40])).
% 6.97/1.26  fof(f51,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 6.97/1.26    inference(cnf_transformation,[],[f29])).
% 6.97/1.26  fof(f29,plain,(
% 6.97/1.26    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.97/1.26    inference(ennf_transformation,[],[f4])).
% 6.97/1.26  fof(f4,axiom,(
% 6.97/1.26    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 6.97/1.26  fof(f132,plain,(
% 6.97/1.26    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 6.97/1.26    inference(superposition,[],[f47,f59])).
% 6.97/1.26  fof(f47,plain,(
% 6.97/1.26    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.97/1.26    inference(cnf_transformation,[],[f7])).
% 6.97/1.26  fof(f7,axiom,(
% 6.97/1.26    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.97/1.26  fof(f506,plain,(
% 6.97/1.26    ( ! [X28,X27] : (r1_tarski(k4_xboole_0(X27,k1_xboole_0),k2_xboole_0(k4_xboole_0(X27,k1_xboole_0),X28))) )),
% 6.97/1.26    inference(superposition,[],[f132,f211])).
% 6.97/1.26  fof(f211,plain,(
% 6.97/1.26    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),X6))) )),
% 6.97/1.26    inference(forward_demodulation,[],[f200,f76])).
% 6.97/1.26  fof(f76,plain,(
% 6.97/1.26    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 6.97/1.26    inference(resolution,[],[f73,f47])).
% 6.97/1.26  fof(f200,plain,(
% 6.97/1.26    ( ! [X6,X5] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),X6))) )),
% 6.97/1.26    inference(superposition,[],[f56,f157])).
% 6.97/1.26  fof(f12282,plain,(
% 6.97/1.26    ~r1_tarski(sK1,k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | spl2_165),
% 6.97/1.26    inference(avatar_component_clause,[],[f12280])).
% 6.97/1.26  fof(f12280,plain,(
% 6.97/1.26    spl2_165 <=> r1_tarski(sK1,k2_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_165])])).
% 6.97/1.26  fof(f61,plain,(
% 6.97/1.26    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.97/1.26    inference(equality_resolution,[],[f54])).
% 6.97/1.26  fof(f54,plain,(
% 6.97/1.26    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.97/1.26    inference(cnf_transformation,[],[f3])).
% 6.97/1.26  fof(f3,axiom,(
% 6.97/1.26    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.97/1.26  fof(f12351,plain,(
% 6.97/1.26    spl2_172 | ~spl2_165 | ~spl2_163),
% 6.97/1.26    inference(avatar_split_clause,[],[f12344,f12271,f12280,f12348])).
% 6.97/1.26  fof(f12271,plain,(
% 6.97/1.26    spl2_163 <=> r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1)),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_163])])).
% 6.97/1.26  fof(f12344,plain,(
% 6.97/1.26    ~r1_tarski(sK1,k2_xboole_0(sK1,k2_tops_1(sK0,sK1))) | sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_163),
% 6.97/1.26    inference(resolution,[],[f12272,f55])).
% 6.97/1.26  fof(f55,plain,(
% 6.97/1.26    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 6.97/1.26    inference(cnf_transformation,[],[f3])).
% 6.97/1.26  fof(f12272,plain,(
% 6.97/1.26    r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1) | ~spl2_163),
% 6.97/1.26    inference(avatar_component_clause,[],[f12271])).
% 6.97/1.26  fof(f12338,plain,(
% 6.97/1.26    ~spl2_22 | ~spl2_3 | ~spl2_118 | ~spl2_135 | spl2_163),
% 6.97/1.26    inference(avatar_split_clause,[],[f12336,f12271,f10608,f9166,f178,f1564])).
% 6.97/1.26  fof(f10608,plain,(
% 6.97/1.26    spl2_135 <=> r1_tarski(k2_pre_topc(sK0,sK1),sK1)),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).
% 6.97/1.26  fof(f12336,plain,(
% 6.97/1.26    ~r1_tarski(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_163),
% 6.97/1.26    inference(superposition,[],[f12273,f745])).
% 6.97/1.26  fof(f12273,plain,(
% 6.97/1.26    ~r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1) | spl2_163),
% 6.97/1.26    inference(avatar_component_clause,[],[f12271])).
% 6.97/1.26  fof(f10824,plain,(
% 6.97/1.26    spl2_139),
% 6.97/1.26    inference(avatar_contradiction_clause,[],[f10820])).
% 6.97/1.26  fof(f10820,plain,(
% 6.97/1.26    $false | spl2_139),
% 6.97/1.26    inference(unit_resulting_resolution,[],[f61,f61,f10634,f2250])).
% 6.97/1.26  fof(f2250,plain,(
% 6.97/1.26    ( ! [X50,X51,X49] : (~r1_tarski(X50,X49) | ~r1_tarski(X49,X51) | r1_tarski(X50,X51)) )),
% 6.97/1.26    inference(superposition,[],[f2206,f124])).
% 6.97/1.26  fof(f2206,plain,(
% 6.97/1.26    ( ! [X6,X7,X5] : (r1_tarski(k4_xboole_0(X5,X7),X6) | ~r1_tarski(X5,X6)) )),
% 6.97/1.26    inference(superposition,[],[f2089,f86])).
% 6.97/1.26  fof(f86,plain,(
% 6.97/1.26    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(X2,X4) | ~r1_tarski(X2,X3)) )),
% 6.97/1.26    inference(superposition,[],[f56,f60])).
% 6.97/1.26  fof(f2089,plain,(
% 6.97/1.26    ( ! [X17,X15,X16] : (r1_tarski(k4_xboole_0(X16,k2_xboole_0(k4_xboole_0(X16,X15),X17)),X15)) )),
% 6.97/1.26    inference(forward_demodulation,[],[f1939,f56])).
% 6.97/1.26  fof(f1939,plain,(
% 6.97/1.26    ( ! [X17,X15,X16] : (r1_tarski(k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),X17),X15)) )),
% 6.97/1.26    inference(superposition,[],[f47,f133])).
% 6.97/1.26  fof(f133,plain,(
% 6.97/1.26    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,X5),X6)) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6)) )),
% 6.97/1.26    inference(superposition,[],[f56,f59])).
% 6.97/1.26  fof(f10634,plain,(
% 6.97/1.26    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | spl2_139),
% 6.97/1.26    inference(avatar_component_clause,[],[f10632])).
% 6.97/1.26  fof(f10632,plain,(
% 6.97/1.26    spl2_139 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_139])])).
% 6.97/1.26  fof(f10660,plain,(
% 6.97/1.26    ~spl2_139 | spl2_135 | ~spl2_134),
% 6.97/1.26    inference(avatar_split_clause,[],[f10648,f10539,f10608,f10632])).
% 6.97/1.26  fof(f10539,plain,(
% 6.97/1.26    spl2_134 <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1)),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_134])])).
% 6.97/1.26  fof(f10648,plain,(
% 6.97/1.26    r1_tarski(k2_pre_topc(sK0,sK1),sK1) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl2_134),
% 6.97/1.26    inference(superposition,[],[f10572,f306])).
% 6.97/1.26  fof(f10572,plain,(
% 6.97/1.26    r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0),sK1) | ~spl2_134),
% 6.97/1.26    inference(superposition,[],[f132,f10545])).
% 6.97/1.26  fof(f10545,plain,(
% 6.97/1.26    k1_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_134),
% 6.97/1.26    inference(resolution,[],[f10541,f4207])).
% 6.97/1.26  fof(f4207,plain,(
% 6.97/1.26    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(X3,X2),X2) | k1_xboole_0 = k4_xboole_0(X3,X2)) )),
% 6.97/1.26    inference(forward_demodulation,[],[f4125,f210])).
% 6.97/1.26  fof(f210,plain,(
% 6.97/1.26    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X5)))) )),
% 6.97/1.26    inference(forward_demodulation,[],[f209,f40])).
% 6.97/1.26  fof(f209,plain,(
% 6.97/1.26    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,k1_xboole_0))))) )),
% 6.97/1.26    inference(forward_demodulation,[],[f194,f56])).
% 6.97/1.26  fof(f194,plain,(
% 6.97/1.26    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)))) )),
% 6.97/1.26    inference(superposition,[],[f157,f56])).
% 6.97/1.26  fof(f4125,plain,(
% 6.97/1.26    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(X3,k2_xboole_0(X2,k4_xboole_0(X3,X2))) | ~r1_tarski(k4_xboole_0(X3,X2),X2)) )),
% 6.97/1.26    inference(superposition,[],[f96,f46])).
% 6.97/1.26  fof(f46,plain,(
% 6.97/1.26    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 6.97/1.26    inference(cnf_transformation,[],[f19])).
% 6.97/1.26  fof(f19,plain,(
% 6.97/1.26    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 6.97/1.26    inference(rectify,[],[f2])).
% 6.97/1.26  fof(f2,axiom,(
% 6.97/1.26    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 6.97/1.26  fof(f96,plain,(
% 6.97/1.26    ( ! [X4,X5,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) | ~r1_tarski(k4_xboole_0(X3,X4),X5)) )),
% 6.97/1.26    inference(forward_demodulation,[],[f88,f56])).
% 6.97/1.26  fof(f88,plain,(
% 6.97/1.26    ( ! [X4,X5,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5))) | ~r1_tarski(k4_xboole_0(X3,X4),X5)) )),
% 6.97/1.26    inference(superposition,[],[f56,f60])).
% 6.97/1.26  fof(f10541,plain,(
% 6.97/1.26    r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) | ~spl2_134),
% 6.97/1.26    inference(avatar_component_clause,[],[f10539])).
% 6.97/1.26  fof(f10542,plain,(
% 6.97/1.26    ~spl2_22 | ~spl2_3 | ~spl2_118 | spl2_134 | ~spl2_4),
% 6.97/1.26    inference(avatar_split_clause,[],[f10526,f182,f10539,f9166,f178,f1564])).
% 6.97/1.26  fof(f10526,plain,(
% 6.97/1.26    r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_4),
% 6.97/1.26    inference(superposition,[],[f6064,f745])).
% 6.97/1.26  fof(f6064,plain,(
% 6.97/1.26    ( ! [X18] : (r1_tarski(k4_xboole_0(k2_xboole_0(X18,k2_tops_1(sK0,sK1)),X18),sK1)) ) | ~spl2_4),
% 6.97/1.26    inference(resolution,[],[f6043,f5168])).
% 6.97/1.26  fof(f5168,plain,(
% 6.97/1.26    ( ! [X15] : (~r1_tarski(X15,k2_tops_1(sK0,sK1)) | r1_tarski(X15,sK1)) ) | ~spl2_4),
% 6.97/1.26    inference(superposition,[],[f4791,f184])).
% 6.97/1.26  fof(f4791,plain,(
% 6.97/1.26    ( ! [X21,X22,X20] : (~r1_tarski(X20,k4_xboole_0(X21,X22)) | r1_tarski(X20,X21)) )),
% 6.97/1.26    inference(superposition,[],[f3600,f60])).
% 6.97/1.26  fof(f3600,plain,(
% 6.97/1.26    ( ! [X28,X26,X27] : (r1_tarski(k4_xboole_0(X28,k4_xboole_0(X28,k4_xboole_0(X26,X27))),X26)) )),
% 6.97/1.26    inference(superposition,[],[f47,f152])).
% 6.97/1.26  fof(f152,plain,(
% 6.97/1.26    ( ! [X8,X7,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9))))) )),
% 6.97/1.26    inference(forward_demodulation,[],[f125,f56])).
% 6.97/1.26  fof(f125,plain,(
% 6.97/1.26    ( ! [X8,X7,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X7,X8))) = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(k4_xboole_0(X7,X8),X9)))) )),
% 6.97/1.26    inference(superposition,[],[f59,f56])).
% 6.97/1.26  fof(f6043,plain,(
% 6.97/1.26    ( ! [X26,X27] : (r1_tarski(k4_xboole_0(k2_xboole_0(X26,X27),X26),X27)) )),
% 6.97/1.26    inference(forward_demodulation,[],[f6007,f40])).
% 6.97/1.26  fof(f6007,plain,(
% 6.97/1.26    ( ! [X26,X27] : (r1_tarski(k4_xboole_0(k2_xboole_0(X26,X27),k2_xboole_0(X26,k1_xboole_0)),X27)) )),
% 6.97/1.26    inference(superposition,[],[f170,f748])).
% 6.97/1.26  fof(f748,plain,(
% 6.97/1.26    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 6.97/1.26    inference(resolution,[],[f716,f73])).
% 6.97/1.26  fof(f716,plain,(
% 6.97/1.26    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0)) )),
% 6.97/1.26    inference(resolution,[],[f204,f47])).
% 6.97/1.26  fof(f204,plain,(
% 6.97/1.26    ( ! [X14,X13] : (~r1_tarski(k4_xboole_0(X13,k1_xboole_0),X14) | r1_tarski(k4_xboole_0(X13,X14),k1_xboole_0)) )),
% 6.97/1.26    inference(superposition,[],[f102,f157])).
% 6.97/1.26  fof(f102,plain,(
% 6.97/1.26    ( ! [X6,X4,X5] : (r1_tarski(k4_xboole_0(X6,X5),k4_xboole_0(X6,X4)) | ~r1_tarski(X4,X5)) )),
% 6.97/1.26    inference(superposition,[],[f91,f51])).
% 6.97/1.26  fof(f91,plain,(
% 6.97/1.26    ( ! [X6,X8,X7] : (r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X8)),k4_xboole_0(X6,X7))) )),
% 6.97/1.26    inference(superposition,[],[f47,f56])).
% 6.97/1.26  fof(f170,plain,(
% 6.97/1.26    ( ! [X8,X7,X9] : (r1_tarski(k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9)))),X9)) )),
% 6.97/1.26    inference(forward_demodulation,[],[f163,f56])).
% 6.97/1.26  fof(f163,plain,(
% 6.97/1.26    ( ! [X8,X7,X9] : (r1_tarski(k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X9))),X9)) )),
% 6.97/1.26    inference(superposition,[],[f132,f56])).
% 6.97/1.26  fof(f9179,plain,(
% 6.97/1.26    spl2_118),
% 6.97/1.26    inference(avatar_contradiction_clause,[],[f9177])).
% 6.97/1.26  fof(f9177,plain,(
% 6.97/1.26    $false | spl2_118),
% 6.97/1.26    inference(unit_resulting_resolution,[],[f39,f37,f9168,f52])).
% 6.97/1.26  fof(f52,plain,(
% 6.97/1.26    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.97/1.26    inference(cnf_transformation,[],[f31])).
% 6.97/1.26  fof(f31,plain,(
% 6.97/1.26    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 6.97/1.26    inference(flattening,[],[f30])).
% 6.97/1.26  fof(f30,plain,(
% 6.97/1.26    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 6.97/1.26    inference(ennf_transformation,[],[f13])).
% 6.97/1.26  fof(f13,axiom,(
% 6.97/1.26    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 6.97/1.26  fof(f9168,plain,(
% 6.97/1.26    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_118),
% 6.97/1.26    inference(avatar_component_clause,[],[f9166])).
% 6.97/1.26  fof(f2431,plain,(
% 6.97/1.26    ~spl2_3 | spl2_4 | ~spl2_2),
% 6.97/1.26    inference(avatar_split_clause,[],[f2429,f68,f182,f178])).
% 6.97/1.26  fof(f2429,plain,(
% 6.97/1.26    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 6.97/1.26    inference(superposition,[],[f57,f69])).
% 6.97/1.26  fof(f69,plain,(
% 6.97/1.26    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 6.97/1.26    inference(avatar_component_clause,[],[f68])).
% 6.97/1.26  fof(f2334,plain,(
% 6.97/1.26    spl2_31),
% 6.97/1.26    inference(avatar_contradiction_clause,[],[f2333])).
% 6.97/1.26  fof(f2333,plain,(
% 6.97/1.26    $false | spl2_31),
% 6.97/1.26    inference(subsumption_resolution,[],[f38,f2331])).
% 6.97/1.26  fof(f2331,plain,(
% 6.97/1.26    ~v2_pre_topc(sK0) | spl2_31),
% 6.97/1.26    inference(avatar_component_clause,[],[f2329])).
% 6.97/1.26  fof(f2329,plain,(
% 6.97/1.26    spl2_31 <=> v2_pre_topc(sK0)),
% 6.97/1.26    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 6.97/1.26  fof(f38,plain,(
% 6.97/1.26    v2_pre_topc(sK0)),
% 6.97/1.26    inference(cnf_transformation,[],[f21])).
% 6.97/1.26  fof(f2332,plain,(
% 6.97/1.26    spl2_1 | ~spl2_22 | ~spl2_31 | ~spl2_3 | ~spl2_23),
% 6.97/1.26    inference(avatar_split_clause,[],[f1578,f1569,f178,f2329,f1564,f64])).
% 6.97/1.26  fof(f1578,plain,(
% 6.97/1.26    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~spl2_23),
% 6.97/1.26    inference(trivial_inequality_removal,[],[f1577])).
% 6.97/1.26  fof(f1577,plain,(
% 6.97/1.26    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~spl2_23),
% 6.97/1.26    inference(superposition,[],[f43,f1571])).
% 6.97/1.26  fof(f1571,plain,(
% 6.97/1.26    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_23),
% 6.97/1.26    inference(avatar_component_clause,[],[f1569])).
% 6.97/1.26  fof(f43,plain,(
% 6.97/1.26    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 6.97/1.26    inference(cnf_transformation,[],[f25])).
% 6.97/1.26  fof(f25,plain,(
% 6.97/1.26    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.97/1.26    inference(flattening,[],[f24])).
% 6.97/1.26  fof(f24,plain,(
% 6.97/1.26    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.97/1.26    inference(ennf_transformation,[],[f12])).
% 6.97/1.26  fof(f12,axiom,(
% 6.97/1.26    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 6.97/1.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 6.97/1.26  fof(f1574,plain,(
% 6.97/1.26    spl2_22),
% 6.97/1.26    inference(avatar_contradiction_clause,[],[f1573])).
% 6.97/1.26  fof(f1573,plain,(
% 6.97/1.26    $false | spl2_22),
% 6.97/1.26    inference(subsumption_resolution,[],[f39,f1566])).
% 6.97/1.26  fof(f1566,plain,(
% 6.97/1.26    ~l1_pre_topc(sK0) | spl2_22),
% 6.97/1.26    inference(avatar_component_clause,[],[f1564])).
% 6.97/1.26  fof(f188,plain,(
% 6.97/1.26    spl2_3),
% 6.97/1.26    inference(avatar_contradiction_clause,[],[f187])).
% 6.97/1.26  fof(f187,plain,(
% 6.97/1.26    $false | spl2_3),
% 6.97/1.26    inference(subsumption_resolution,[],[f37,f180])).
% 6.97/1.26  fof(f180,plain,(
% 6.97/1.26    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 6.97/1.26    inference(avatar_component_clause,[],[f178])).
% 6.97/1.26  fof(f72,plain,(
% 6.97/1.26    spl2_1 | spl2_2),
% 6.97/1.26    inference(avatar_split_clause,[],[f35,f68,f64])).
% 6.97/1.26  fof(f35,plain,(
% 6.97/1.26    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 6.97/1.26    inference(cnf_transformation,[],[f21])).
% 6.97/1.26  fof(f71,plain,(
% 6.97/1.26    ~spl2_1 | ~spl2_2),
% 6.97/1.26    inference(avatar_split_clause,[],[f36,f68,f64])).
% 6.97/1.26  fof(f36,plain,(
% 6.97/1.26    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 6.97/1.26    inference(cnf_transformation,[],[f21])).
% 6.97/1.26  % SZS output end Proof for theBenchmark
% 6.97/1.26  % (17514)------------------------------
% 6.97/1.26  % (17514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.97/1.26  % (17514)Termination reason: Refutation
% 6.97/1.26  
% 6.97/1.26  % (17514)Memory used [KB]: 13560
% 6.97/1.26  % (17514)Time elapsed: 0.828 s
% 6.97/1.26  % (17514)------------------------------
% 6.97/1.26  % (17514)------------------------------
% 6.97/1.26  % (17500)Success in time 0.87 s
%------------------------------------------------------------------------------
