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
% DateTime   : Thu Dec  3 13:11:40 EST 2020

% Result     : Theorem 3.26s
% Output     : Refutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 318 expanded)
%              Number of leaves         :   44 ( 136 expanded)
%              Depth                    :   10
%              Number of atoms          :  468 ( 805 expanded)
%              Number of equality atoms :   77 ( 131 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3769,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f94,f125,f132,f142,f153,f169,f310,f316,f381,f430,f573,f682,f813,f995,f1029,f1292,f1363,f1420,f1429,f1443,f1530,f1550,f3766,f3767,f3768])).

fof(f3768,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3767,plain,
    ( k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 != k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3766,plain,
    ( spl2_162
    | ~ spl2_9
    | ~ spl2_62
    | ~ spl2_75
    | ~ spl2_86 ),
    inference(avatar_split_clause,[],[f3754,f1418,f1290,f993,f151,f3764])).

fof(f3764,plain,
    ( spl2_162
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_162])])).

fof(f151,plain,
    ( spl2_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f993,plain,
    ( spl2_62
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f1290,plain,
    ( spl2_75
  <=> m1_subset_1(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f1418,plain,
    ( spl2_86
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).

fof(f3754,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_9
    | ~ spl2_62
    | ~ spl2_75
    | ~ spl2_86 ),
    inference(forward_demodulation,[],[f3753,f160])).

fof(f160,plain,
    ( ! [X4] : k9_subset_1(k2_pre_topc(sK0,sK1),X4,X4) = X4
    | ~ spl2_9 ),
    inference(resolution,[],[f152,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f152,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f3753,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1)
    | ~ spl2_9
    | ~ spl2_62
    | ~ spl2_75
    | ~ spl2_86 ),
    inference(forward_demodulation,[],[f3752,f994])).

fof(f994,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f993])).

fof(f3752,plain,
    ( k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_9
    | ~ spl2_75
    | ~ spl2_86 ),
    inference(forward_demodulation,[],[f3745,f1419])).

fof(f1419,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_86 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f3745,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl2_9
    | ~ spl2_75 ),
    inference(resolution,[],[f163,f1291])).

fof(f1291,plain,
    ( m1_subset_1(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f1290])).

fof(f163,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | k4_xboole_0(sK1,X1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X1)) )
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f155,f154])).

fof(f154,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0)
    | ~ spl2_9 ),
    inference(resolution,[],[f152,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f155,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X1)) )
    | ~ spl2_9 ),
    inference(resolution,[],[f152,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f1550,plain,
    ( spl2_94
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f724,f314,f167,f1548])).

fof(f1548,plain,
    ( spl2_94
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).

fof(f167,plain,
    ( spl2_10
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f314,plain,
    ( spl2_22
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f724,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_10
    | ~ spl2_22 ),
    inference(superposition,[],[f177,f315])).

fof(f315,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f314])).

fof(f177,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)
    | ~ spl2_10 ),
    inference(resolution,[],[f168,f62])).

fof(f168,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f1530,plain,
    ( spl2_92
    | ~ spl2_64
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f444,f428,f1027,f1527])).

fof(f1527,plain,
    ( spl2_92
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f1027,plain,
    ( spl2_64
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f428,plain,
    ( spl2_30
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f444,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_30 ),
    inference(resolution,[],[f429,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f429,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f428])).

fof(f1443,plain,
    ( ~ spl2_5
    | ~ spl2_10
    | ~ spl2_62 ),
    inference(avatar_split_clause,[],[f1030,f993,f167,f127])).

fof(f127,plain,
    ( spl2_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1030,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_10
    | ~ spl2_62 ),
    inference(subsumption_resolution,[],[f996,f994])).

fof(f996,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f55,f177])).

fof(f55,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f1429,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) != k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1420,plain,
    ( spl2_86
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f164,f151,f1418])).

fof(f164,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f161,f157])).

fof(f157,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_9 ),
    inference(resolution,[],[f152,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f161,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl2_9 ),
    inference(resolution,[],[f152,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1363,plain,
    ( spl2_83
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f157,f151,f1361])).

fof(f1361,plain,
    ( spl2_83
  <=> k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).

fof(f1292,plain,
    ( spl2_75
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f165,f151,f1290])).

fof(f165,plain,
    ( m1_subset_1(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f162,f157])).

fof(f162,plain,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_9 ),
    inference(resolution,[],[f152,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1029,plain,
    ( spl2_64
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f1022,f127,f92,f88,f1027])).

fof(f88,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f92,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1022,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f1019,f82])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1019,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(resolution,[],[f998,f93])).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f998,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f118,f128])).

fof(f128,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f101,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl2_3 ),
    inference(resolution,[],[f93,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
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

fof(f995,plain,
    ( spl2_62
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f723,f167,f130,f993])).

fof(f130,plain,
    ( spl2_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f723,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(superposition,[],[f177,f131])).

fof(f131,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f813,plain,
    ( spl2_47
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_40 ),
    inference(avatar_split_clause,[],[f710,f680,f88,f84,f811])).

fof(f811,plain,
    ( spl2_47
  <=> v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f84,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f680,plain,
    ( spl2_40
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f710,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_40 ),
    inference(subsumption_resolution,[],[f709,f85])).

fof(f85,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f709,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ spl2_2
    | ~ spl2_40 ),
    inference(subsumption_resolution,[],[f693,f89])).

fof(f693,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ spl2_40 ),
    inference(resolution,[],[f681,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f681,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f680])).

fof(f682,plain,
    ( spl2_40
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f604,f571,f680])).

fof(f571,plain,
    ( spl2_38
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f604,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_38 ),
    inference(resolution,[],[f572,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f572,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f571])).

fof(f573,plain,
    ( spl2_38
    | ~ spl2_4
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f563,f428,f123,f571])).

fof(f123,plain,
    ( spl2_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f563,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_30 ),
    inference(resolution,[],[f443,f124])).

fof(f124,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl2_30 ),
    inference(resolution,[],[f429,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f430,plain,
    ( spl2_30
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f426,f379,f428])).

fof(f379,plain,
    ( spl2_27
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f426,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_27 ),
    inference(superposition,[],[f74,f380])).

fof(f380,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f379])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f381,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f311,f308,f92,f379])).

fof(f308,plain,
    ( spl2_21
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f311,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(superposition,[],[f309,f102])).

fof(f102,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl2_3 ),
    inference(resolution,[],[f93,f62])).

fof(f309,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f308])).

fof(f316,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f111,f92,f88,f314])).

fof(f111,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f95,f89])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f93,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f310,plain,
    ( spl2_21
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f112,f92,f88,f308])).

fof(f112,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f96,f89])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f93,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f169,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f113,f92,f88,f167])).

fof(f113,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f97,f89])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f93,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f153,plain,
    ( spl2_9
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f147,f140,f151])).

fof(f140,plain,
    ( spl2_7
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f147,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_7 ),
    inference(resolution,[],[f141,f72])).

fof(f141,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( spl2_7
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f114,f92,f88,f140])).

fof(f114,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f98,f89])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f93,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f132,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f54,f130,f127])).

fof(f54,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f125,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f104,f92,f123])).

fof(f104,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f93,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f56,f92])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f58,f88])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f57,f84])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (9114)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.49  % (9121)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.49  % (9137)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.49  % (9120)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (9134)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (9111)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (9118)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (9115)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (9126)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (9117)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (9132)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (9110)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (9124)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (9113)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (9112)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (9138)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (9119)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (9139)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (9116)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (9131)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (9133)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (9136)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (9123)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (9130)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (9125)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (9127)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (9128)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (9135)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (9122)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (9129)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 3.26/0.80  % (9112)Time limit reached!
% 3.26/0.80  % (9112)------------------------------
% 3.26/0.80  % (9112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.81  % (9134)Time limit reached!
% 3.26/0.81  % (9134)------------------------------
% 3.26/0.81  % (9134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.81  % (9134)Termination reason: Time limit
% 3.26/0.81  % (9134)Termination phase: Saturation
% 3.26/0.81  
% 3.26/0.81  % (9134)Memory used [KB]: 13816
% 3.26/0.81  % (9134)Time elapsed: 0.400 s
% 3.26/0.81  % (9134)------------------------------
% 3.26/0.81  % (9134)------------------------------
% 3.26/0.82  % (9112)Termination reason: Time limit
% 3.26/0.82  % (9112)Termination phase: Saturation
% 3.26/0.82  
% 3.26/0.82  % (9112)Memory used [KB]: 6652
% 3.26/0.82  % (9112)Time elapsed: 0.400 s
% 3.26/0.82  % (9112)------------------------------
% 3.26/0.82  % (9112)------------------------------
% 3.26/0.84  % (9136)Refutation found. Thanks to Tanya!
% 3.26/0.84  % SZS status Theorem for theBenchmark
% 3.26/0.84  % SZS output start Proof for theBenchmark
% 3.26/0.84  fof(f3769,plain,(
% 3.26/0.84    $false),
% 3.26/0.84    inference(avatar_sat_refutation,[],[f86,f90,f94,f125,f132,f142,f153,f169,f310,f316,f381,f430,f573,f682,f813,f995,f1029,f1292,f1363,f1420,f1429,f1443,f1530,f1550,f3766,f3767,f3768])).
% 3.26/0.84  fof(f3768,plain,(
% 3.26/0.84    sK1 != k1_tops_1(sK0,sK1) | k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 3.26/0.84    introduced(theory_tautology_sat_conflict,[])).
% 3.26/0.84  fof(f3767,plain,(
% 3.26/0.84    k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)),
% 3.26/0.84    introduced(theory_tautology_sat_conflict,[])).
% 3.26/0.84  fof(f3766,plain,(
% 3.26/0.84    spl2_162 | ~spl2_9 | ~spl2_62 | ~spl2_75 | ~spl2_86),
% 3.26/0.84    inference(avatar_split_clause,[],[f3754,f1418,f1290,f993,f151,f3764])).
% 3.26/0.84  fof(f3764,plain,(
% 3.26/0.84    spl2_162 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_162])])).
% 3.26/0.84  fof(f151,plain,(
% 3.26/0.84    spl2_9 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.26/0.84  fof(f993,plain,(
% 3.26/0.84    spl2_62 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).
% 3.26/0.84  fof(f1290,plain,(
% 3.26/0.84    spl2_75 <=> m1_subset_1(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 3.26/0.84  fof(f1418,plain,(
% 3.26/0.84    spl2_86 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_86])])).
% 3.26/0.84  fof(f3754,plain,(
% 3.26/0.84    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_9 | ~spl2_62 | ~spl2_75 | ~spl2_86)),
% 3.26/0.84    inference(forward_demodulation,[],[f3753,f160])).
% 3.26/0.84  fof(f160,plain,(
% 3.26/0.84    ( ! [X4] : (k9_subset_1(k2_pre_topc(sK0,sK1),X4,X4) = X4) ) | ~spl2_9),
% 3.26/0.84    inference(resolution,[],[f152,f78])).
% 3.26/0.84  fof(f78,plain,(
% 3.26/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 3.26/0.84    inference(cnf_transformation,[],[f51])).
% 3.26/0.84  fof(f51,plain,(
% 3.26/0.84    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.26/0.84    inference(ennf_transformation,[],[f15])).
% 3.26/0.84  fof(f15,axiom,(
% 3.26/0.84    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 3.26/0.84  fof(f152,plain,(
% 3.26/0.84    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_9),
% 3.26/0.84    inference(avatar_component_clause,[],[f151])).
% 3.26/0.84  fof(f3753,plain,(
% 3.26/0.84    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) | (~spl2_9 | ~spl2_62 | ~spl2_75 | ~spl2_86)),
% 3.26/0.84    inference(forward_demodulation,[],[f3752,f994])).
% 3.26/0.84  fof(f994,plain,(
% 3.26/0.84    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_62),
% 3.26/0.84    inference(avatar_component_clause,[],[f993])).
% 3.26/0.84  fof(f3752,plain,(
% 3.26/0.84    k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | (~spl2_9 | ~spl2_75 | ~spl2_86)),
% 3.26/0.84    inference(forward_demodulation,[],[f3745,f1419])).
% 3.26/0.84  fof(f1419,plain,(
% 3.26/0.84    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_86),
% 3.26/0.84    inference(avatar_component_clause,[],[f1418])).
% 3.26/0.84  fof(f3745,plain,(
% 3.26/0.84    k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))) | (~spl2_9 | ~spl2_75)),
% 3.26/0.84    inference(resolution,[],[f163,f1291])).
% 3.26/0.84  fof(f1291,plain,(
% 3.26/0.84    m1_subset_1(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_75),
% 3.26/0.84    inference(avatar_component_clause,[],[f1290])).
% 3.26/0.84  fof(f163,plain,(
% 3.26/0.84    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | k4_xboole_0(sK1,X1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X1))) ) | ~spl2_9),
% 3.26/0.84    inference(forward_demodulation,[],[f155,f154])).
% 3.26/0.84  fof(f154,plain,(
% 3.26/0.84    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0)) ) | ~spl2_9),
% 3.26/0.84    inference(resolution,[],[f152,f62])).
% 3.26/0.84  fof(f62,plain,(
% 3.26/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 3.26/0.84    inference(cnf_transformation,[],[f34])).
% 3.26/0.84  fof(f34,plain,(
% 3.26/0.84    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.26/0.84    inference(ennf_transformation,[],[f17])).
% 3.26/0.84  fof(f17,axiom,(
% 3.26/0.84    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.26/0.84  fof(f155,plain,(
% 3.26/0.84    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),X1))) ) | ~spl2_9),
% 3.26/0.84    inference(resolution,[],[f152,f63])).
% 3.26/0.84  fof(f63,plain,(
% 3.26/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 3.26/0.84    inference(cnf_transformation,[],[f35])).
% 3.26/0.84  fof(f35,plain,(
% 3.26/0.84    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.26/0.84    inference(ennf_transformation,[],[f19])).
% 3.26/0.84  fof(f19,axiom,(
% 3.26/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 3.26/0.84  fof(f1550,plain,(
% 3.26/0.84    spl2_94 | ~spl2_10 | ~spl2_22),
% 3.26/0.84    inference(avatar_split_clause,[],[f724,f314,f167,f1548])).
% 3.26/0.84  fof(f1548,plain,(
% 3.26/0.84    spl2_94 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).
% 3.26/0.84  fof(f167,plain,(
% 3.26/0.84    spl2_10 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 3.26/0.84  fof(f314,plain,(
% 3.26/0.84    spl2_22 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 3.26/0.84  fof(f724,plain,(
% 3.26/0.84    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_10 | ~spl2_22)),
% 3.26/0.84    inference(superposition,[],[f177,f315])).
% 3.26/0.84  fof(f315,plain,(
% 3.26/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_22),
% 3.26/0.84    inference(avatar_component_clause,[],[f314])).
% 3.26/0.84  fof(f177,plain,(
% 3.26/0.84    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)) ) | ~spl2_10),
% 3.26/0.84    inference(resolution,[],[f168,f62])).
% 3.26/0.84  fof(f168,plain,(
% 3.26/0.84    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_10),
% 3.26/0.84    inference(avatar_component_clause,[],[f167])).
% 3.26/0.84  fof(f1530,plain,(
% 3.26/0.84    spl2_92 | ~spl2_64 | ~spl2_30),
% 3.26/0.84    inference(avatar_split_clause,[],[f444,f428,f1027,f1527])).
% 3.26/0.84  fof(f1527,plain,(
% 3.26/0.84    spl2_92 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 3.26/0.84  fof(f1027,plain,(
% 3.26/0.84    spl2_64 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 3.26/0.84  fof(f428,plain,(
% 3.26/0.84    spl2_30 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 3.26/0.84  fof(f444,plain,(
% 3.26/0.84    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1) | ~spl2_30),
% 3.26/0.84    inference(resolution,[],[f429,f61])).
% 3.26/0.84  fof(f61,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 3.26/0.84    inference(cnf_transformation,[],[f2])).
% 3.26/0.84  fof(f2,axiom,(
% 3.26/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.26/0.84  fof(f429,plain,(
% 3.26/0.84    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_30),
% 3.26/0.84    inference(avatar_component_clause,[],[f428])).
% 3.26/0.84  fof(f1443,plain,(
% 3.26/0.84    ~spl2_5 | ~spl2_10 | ~spl2_62),
% 3.26/0.84    inference(avatar_split_clause,[],[f1030,f993,f167,f127])).
% 3.26/0.84  fof(f127,plain,(
% 3.26/0.84    spl2_5 <=> v3_pre_topc(sK1,sK0)),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.26/0.84  fof(f1030,plain,(
% 3.26/0.84    ~v3_pre_topc(sK1,sK0) | (~spl2_10 | ~spl2_62)),
% 3.26/0.84    inference(subsumption_resolution,[],[f996,f994])).
% 3.26/0.84  fof(f996,plain,(
% 3.26/0.84    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0) | ~spl2_10),
% 3.26/0.84    inference(forward_demodulation,[],[f55,f177])).
% 3.26/0.84  fof(f55,plain,(
% 3.26/0.84    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.26/0.84    inference(cnf_transformation,[],[f33])).
% 3.26/0.84  fof(f33,plain,(
% 3.26/0.84    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.26/0.84    inference(flattening,[],[f32])).
% 3.26/0.84  fof(f32,plain,(
% 3.26/0.84    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.26/0.84    inference(ennf_transformation,[],[f31])).
% 3.26/0.84  fof(f31,negated_conjecture,(
% 3.26/0.84    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.26/0.84    inference(negated_conjecture,[],[f30])).
% 3.26/0.84  fof(f30,conjecture,(
% 3.26/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 3.26/0.84  fof(f1429,plain,(
% 3.26/0.84    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) != k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,sK1) != k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.26/0.84    introduced(theory_tautology_sat_conflict,[])).
% 3.26/0.84  fof(f1420,plain,(
% 3.26/0.84    spl2_86 | ~spl2_9),
% 3.26/0.84    inference(avatar_split_clause,[],[f164,f151,f1418])).
% 3.26/0.84  fof(f164,plain,(
% 3.26/0.84    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_9),
% 3.26/0.84    inference(forward_demodulation,[],[f161,f157])).
% 3.26/0.84  fof(f157,plain,(
% 3.26/0.84    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl2_9),
% 3.26/0.84    inference(resolution,[],[f152,f75])).
% 3.26/0.84  fof(f75,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.26/0.84    inference(cnf_transformation,[],[f48])).
% 3.26/0.84  fof(f48,plain,(
% 3.26/0.84    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.26/0.84    inference(ennf_transformation,[],[f11])).
% 3.26/0.84  fof(f11,axiom,(
% 3.26/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.26/0.84  fof(f161,plain,(
% 3.26/0.84    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | ~spl2_9),
% 3.26/0.84    inference(resolution,[],[f152,f79])).
% 3.26/0.84  fof(f79,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 3.26/0.84    inference(cnf_transformation,[],[f52])).
% 3.26/0.84  fof(f52,plain,(
% 3.26/0.84    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.26/0.84    inference(ennf_transformation,[],[f16])).
% 3.26/0.84  fof(f16,axiom,(
% 3.26/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.26/0.84  fof(f1363,plain,(
% 3.26/0.84    spl2_83 | ~spl2_9),
% 3.26/0.84    inference(avatar_split_clause,[],[f157,f151,f1361])).
% 3.26/0.84  fof(f1361,plain,(
% 3.26/0.84    spl2_83 <=> k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).
% 3.26/0.84  fof(f1292,plain,(
% 3.26/0.84    spl2_75 | ~spl2_9),
% 3.26/0.84    inference(avatar_split_clause,[],[f165,f151,f1290])).
% 3.26/0.84  fof(f165,plain,(
% 3.26/0.84    m1_subset_1(k4_xboole_0(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_9),
% 3.26/0.84    inference(forward_demodulation,[],[f162,f157])).
% 3.26/0.84  fof(f162,plain,(
% 3.26/0.84    m1_subset_1(k3_subset_1(k2_pre_topc(sK0,sK1),sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_9),
% 3.26/0.84    inference(resolution,[],[f152,f80])).
% 3.26/0.84  fof(f80,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.26/0.84    inference(cnf_transformation,[],[f53])).
% 3.26/0.84  fof(f53,plain,(
% 3.26/0.84    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.26/0.84    inference(ennf_transformation,[],[f13])).
% 3.26/0.84  fof(f13,axiom,(
% 3.26/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.26/0.84  fof(f1029,plain,(
% 3.26/0.84    spl2_64 | ~spl2_2 | ~spl2_3 | ~spl2_5),
% 3.26/0.84    inference(avatar_split_clause,[],[f1022,f127,f92,f88,f1027])).
% 3.26/0.84  fof(f88,plain,(
% 3.26/0.84    spl2_2 <=> l1_pre_topc(sK0)),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.26/0.84  fof(f92,plain,(
% 3.26/0.84    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.26/0.84  fof(f1022,plain,(
% 3.26/0.84    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 3.26/0.84    inference(subsumption_resolution,[],[f1019,f82])).
% 3.26/0.84  fof(f82,plain,(
% 3.26/0.84    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.26/0.84    inference(equality_resolution,[],[f59])).
% 3.26/0.84  fof(f59,plain,(
% 3.26/0.84    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.26/0.84    inference(cnf_transformation,[],[f2])).
% 3.26/0.84  fof(f1019,plain,(
% 3.26/0.84    ~r1_tarski(sK1,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 3.26/0.84    inference(resolution,[],[f998,f93])).
% 3.26/0.84  fof(f93,plain,(
% 3.26/0.84    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.26/0.84    inference(avatar_component_clause,[],[f92])).
% 3.26/0.84  fof(f998,plain,(
% 3.26/0.84    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_3 | ~spl2_5)),
% 3.26/0.84    inference(subsumption_resolution,[],[f118,f128])).
% 3.26/0.84  fof(f128,plain,(
% 3.26/0.84    v3_pre_topc(sK1,sK0) | ~spl2_5),
% 3.26/0.84    inference(avatar_component_clause,[],[f127])).
% 3.26/0.84  fof(f118,plain,(
% 3.26/0.84    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_3)),
% 3.26/0.84    inference(subsumption_resolution,[],[f101,f89])).
% 3.26/0.84  fof(f89,plain,(
% 3.26/0.84    l1_pre_topc(sK0) | ~spl2_2),
% 3.26/0.84    inference(avatar_component_clause,[],[f88])).
% 3.26/0.84  fof(f101,plain,(
% 3.26/0.84    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | ~spl2_3),
% 3.26/0.84    inference(resolution,[],[f93,f70])).
% 3.26/0.84  fof(f70,plain,(
% 3.26/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 3.26/0.84    inference(cnf_transformation,[],[f45])).
% 3.26/0.84  fof(f45,plain,(
% 3.26/0.84    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.26/0.84    inference(flattening,[],[f44])).
% 3.26/0.84  fof(f44,plain,(
% 3.26/0.84    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.26/0.84    inference(ennf_transformation,[],[f27])).
% 3.26/0.84  fof(f27,axiom,(
% 3.26/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 3.26/0.84  fof(f995,plain,(
% 3.26/0.84    spl2_62 | ~spl2_6 | ~spl2_10),
% 3.26/0.84    inference(avatar_split_clause,[],[f723,f167,f130,f993])).
% 3.26/0.84  fof(f130,plain,(
% 3.26/0.84    spl2_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.26/0.84  fof(f723,plain,(
% 3.26/0.84    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_6 | ~spl2_10)),
% 3.26/0.84    inference(superposition,[],[f177,f131])).
% 3.26/0.84  fof(f131,plain,(
% 3.26/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_6),
% 3.26/0.84    inference(avatar_component_clause,[],[f130])).
% 3.26/0.84  fof(f813,plain,(
% 3.26/0.84    spl2_47 | ~spl2_1 | ~spl2_2 | ~spl2_40),
% 3.26/0.84    inference(avatar_split_clause,[],[f710,f680,f88,f84,f811])).
% 3.26/0.84  fof(f811,plain,(
% 3.26/0.84    spl2_47 <=> v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 3.26/0.84  fof(f84,plain,(
% 3.26/0.84    spl2_1 <=> v2_pre_topc(sK0)),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.26/0.84  fof(f680,plain,(
% 3.26/0.84    spl2_40 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 3.26/0.84  fof(f710,plain,(
% 3.26/0.84    v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_40)),
% 3.26/0.84    inference(subsumption_resolution,[],[f709,f85])).
% 3.26/0.84  fof(f85,plain,(
% 3.26/0.84    v2_pre_topc(sK0) | ~spl2_1),
% 3.26/0.84    inference(avatar_component_clause,[],[f84])).
% 3.26/0.84  fof(f709,plain,(
% 3.26/0.84    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) | (~spl2_2 | ~spl2_40)),
% 3.26/0.84    inference(subsumption_resolution,[],[f693,f89])).
% 3.26/0.84  fof(f693,plain,(
% 3.26/0.84    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) | ~spl2_40),
% 3.26/0.84    inference(resolution,[],[f681,f69])).
% 3.26/0.84  fof(f69,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 3.26/0.84    inference(cnf_transformation,[],[f43])).
% 3.26/0.84  fof(f43,plain,(
% 3.26/0.84    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.26/0.84    inference(flattening,[],[f42])).
% 3.26/0.84  fof(f42,plain,(
% 3.26/0.84    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.26/0.84    inference(ennf_transformation,[],[f25])).
% 3.26/0.84  fof(f25,axiom,(
% 3.26/0.84    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.26/0.84  fof(f681,plain,(
% 3.26/0.84    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_40),
% 3.26/0.84    inference(avatar_component_clause,[],[f680])).
% 3.26/0.84  fof(f682,plain,(
% 3.26/0.84    spl2_40 | ~spl2_38),
% 3.26/0.84    inference(avatar_split_clause,[],[f604,f571,f680])).
% 3.26/0.84  fof(f571,plain,(
% 3.26/0.84    spl2_38 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 3.26/0.84  fof(f604,plain,(
% 3.26/0.84    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_38),
% 3.26/0.84    inference(resolution,[],[f572,f72])).
% 3.26/0.84  fof(f72,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.26/0.84    inference(cnf_transformation,[],[f21])).
% 3.26/0.84  fof(f21,axiom,(
% 3.26/0.84    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.26/0.84  fof(f572,plain,(
% 3.26/0.84    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_38),
% 3.26/0.84    inference(avatar_component_clause,[],[f571])).
% 3.26/0.84  fof(f573,plain,(
% 3.26/0.84    spl2_38 | ~spl2_4 | ~spl2_30),
% 3.26/0.84    inference(avatar_split_clause,[],[f563,f428,f123,f571])).
% 3.26/0.84  fof(f123,plain,(
% 3.26/0.84    spl2_4 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.26/0.84  fof(f563,plain,(
% 3.26/0.84    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl2_4 | ~spl2_30)),
% 3.26/0.84    inference(resolution,[],[f443,f124])).
% 3.26/0.84  fof(f124,plain,(
% 3.26/0.84    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_4),
% 3.26/0.84    inference(avatar_component_clause,[],[f123])).
% 3.26/0.84  fof(f443,plain,(
% 3.26/0.84    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl2_30),
% 3.26/0.84    inference(resolution,[],[f429,f71])).
% 3.26/0.84  fof(f71,plain,(
% 3.26/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 3.26/0.84    inference(cnf_transformation,[],[f47])).
% 3.26/0.84  fof(f47,plain,(
% 3.26/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.26/0.84    inference(flattening,[],[f46])).
% 3.26/0.84  fof(f46,plain,(
% 3.26/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.26/0.84    inference(ennf_transformation,[],[f3])).
% 3.26/0.84  fof(f3,axiom,(
% 3.26/0.84    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.26/0.84  fof(f430,plain,(
% 3.26/0.84    spl2_30 | ~spl2_27),
% 3.26/0.84    inference(avatar_split_clause,[],[f426,f379,f428])).
% 3.26/0.84  fof(f379,plain,(
% 3.26/0.84    spl2_27 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 3.26/0.84  fof(f426,plain,(
% 3.26/0.84    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_27),
% 3.26/0.84    inference(superposition,[],[f74,f380])).
% 3.26/0.84  fof(f380,plain,(
% 3.26/0.84    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_27),
% 3.26/0.84    inference(avatar_component_clause,[],[f379])).
% 3.26/0.84  fof(f74,plain,(
% 3.26/0.84    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.26/0.84    inference(cnf_transformation,[],[f4])).
% 3.26/0.84  fof(f4,axiom,(
% 3.26/0.84    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.26/0.84  fof(f381,plain,(
% 3.26/0.84    spl2_27 | ~spl2_3 | ~spl2_21),
% 3.26/0.84    inference(avatar_split_clause,[],[f311,f308,f92,f379])).
% 3.26/0.84  fof(f308,plain,(
% 3.26/0.84    spl2_21 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 3.26/0.84  fof(f311,plain,(
% 3.26/0.84    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_21)),
% 3.26/0.84    inference(superposition,[],[f309,f102])).
% 3.26/0.84  fof(f102,plain,(
% 3.26/0.84    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)) ) | ~spl2_3),
% 3.26/0.84    inference(resolution,[],[f93,f62])).
% 3.26/0.84  fof(f309,plain,(
% 3.26/0.84    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_21),
% 3.26/0.84    inference(avatar_component_clause,[],[f308])).
% 3.26/0.84  fof(f316,plain,(
% 3.26/0.84    spl2_22 | ~spl2_2 | ~spl2_3),
% 3.26/0.84    inference(avatar_split_clause,[],[f111,f92,f88,f314])).
% 3.26/0.84  fof(f111,plain,(
% 3.26/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.26/0.84    inference(subsumption_resolution,[],[f95,f89])).
% 3.26/0.84  fof(f95,plain,(
% 3.26/0.84    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_3),
% 3.26/0.84    inference(resolution,[],[f93,f64])).
% 3.26/0.84  fof(f64,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 3.26/0.84    inference(cnf_transformation,[],[f36])).
% 3.26/0.84  fof(f36,plain,(
% 3.26/0.84    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.26/0.84    inference(ennf_transformation,[],[f26])).
% 3.26/0.84  fof(f26,axiom,(
% 3.26/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.26/0.84  fof(f310,plain,(
% 3.26/0.84    spl2_21 | ~spl2_2 | ~spl2_3),
% 3.26/0.84    inference(avatar_split_clause,[],[f112,f92,f88,f308])).
% 3.26/0.84  fof(f112,plain,(
% 3.26/0.84    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.26/0.84    inference(subsumption_resolution,[],[f96,f89])).
% 3.26/0.84  fof(f96,plain,(
% 3.26/0.84    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_3),
% 3.26/0.84    inference(resolution,[],[f93,f65])).
% 3.26/0.84  fof(f65,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 3.26/0.84    inference(cnf_transformation,[],[f37])).
% 3.26/0.84  fof(f37,plain,(
% 3.26/0.84    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.26/0.84    inference(ennf_transformation,[],[f29])).
% 3.26/0.84  fof(f29,axiom,(
% 3.26/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.26/0.84  fof(f169,plain,(
% 3.26/0.84    spl2_10 | ~spl2_2 | ~spl2_3),
% 3.26/0.84    inference(avatar_split_clause,[],[f113,f92,f88,f167])).
% 3.26/0.84  fof(f113,plain,(
% 3.26/0.84    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 3.26/0.84    inference(subsumption_resolution,[],[f97,f89])).
% 3.26/0.84  fof(f97,plain,(
% 3.26/0.84    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.26/0.84    inference(resolution,[],[f93,f66])).
% 3.26/0.84  fof(f66,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 3.26/0.84    inference(cnf_transformation,[],[f39])).
% 3.26/0.84  fof(f39,plain,(
% 3.26/0.84    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.26/0.84    inference(flattening,[],[f38])).
% 3.26/0.84  fof(f38,plain,(
% 3.26/0.84    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.26/0.84    inference(ennf_transformation,[],[f23])).
% 3.26/0.84  fof(f23,axiom,(
% 3.26/0.84    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 3.26/0.84  fof(f153,plain,(
% 3.26/0.84    spl2_9 | ~spl2_7),
% 3.26/0.84    inference(avatar_split_clause,[],[f147,f140,f151])).
% 3.26/0.84  fof(f140,plain,(
% 3.26/0.84    spl2_7 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.26/0.84    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 3.26/0.84  fof(f147,plain,(
% 3.26/0.84    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_7),
% 3.26/0.84    inference(resolution,[],[f141,f72])).
% 3.26/0.84  fof(f141,plain,(
% 3.26/0.84    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_7),
% 3.26/0.84    inference(avatar_component_clause,[],[f140])).
% 3.26/0.84  fof(f142,plain,(
% 3.26/0.84    spl2_7 | ~spl2_2 | ~spl2_3),
% 3.26/0.84    inference(avatar_split_clause,[],[f114,f92,f88,f140])).
% 3.26/0.84  fof(f114,plain,(
% 3.26/0.84    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 3.26/0.84    inference(subsumption_resolution,[],[f98,f89])).
% 3.26/0.84  fof(f98,plain,(
% 3.26/0.84    ~l1_pre_topc(sK0) | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl2_3),
% 3.26/0.84    inference(resolution,[],[f93,f67])).
% 3.26/0.84  fof(f67,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 3.26/0.84    inference(cnf_transformation,[],[f40])).
% 3.26/0.84  fof(f40,plain,(
% 3.26/0.84    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.26/0.84    inference(ennf_transformation,[],[f24])).
% 3.26/0.84  fof(f24,axiom,(
% 3.26/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.26/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 3.26/0.84  fof(f132,plain,(
% 3.26/0.84    spl2_5 | spl2_6),
% 3.26/0.84    inference(avatar_split_clause,[],[f54,f130,f127])).
% 3.26/0.84  fof(f54,plain,(
% 3.26/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.26/0.84    inference(cnf_transformation,[],[f33])).
% 3.26/0.84  fof(f125,plain,(
% 3.26/0.84    spl2_4 | ~spl2_3),
% 3.26/0.84    inference(avatar_split_clause,[],[f104,f92,f123])).
% 3.26/0.84  fof(f104,plain,(
% 3.26/0.84    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 3.26/0.84    inference(resolution,[],[f93,f73])).
% 3.26/0.84  fof(f73,plain,(
% 3.26/0.84    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.26/0.84    inference(cnf_transformation,[],[f21])).
% 3.26/0.84  fof(f94,plain,(
% 3.26/0.84    spl2_3),
% 3.26/0.84    inference(avatar_split_clause,[],[f56,f92])).
% 3.26/0.84  fof(f56,plain,(
% 3.26/0.84    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.26/0.84    inference(cnf_transformation,[],[f33])).
% 3.26/0.84  fof(f90,plain,(
% 3.26/0.84    spl2_2),
% 3.26/0.84    inference(avatar_split_clause,[],[f58,f88])).
% 3.26/0.84  fof(f58,plain,(
% 3.26/0.84    l1_pre_topc(sK0)),
% 3.26/0.84    inference(cnf_transformation,[],[f33])).
% 3.26/0.84  fof(f86,plain,(
% 3.26/0.84    spl2_1),
% 3.26/0.84    inference(avatar_split_clause,[],[f57,f84])).
% 3.26/0.84  fof(f57,plain,(
% 3.26/0.84    v2_pre_topc(sK0)),
% 3.26/0.84    inference(cnf_transformation,[],[f33])).
% 3.26/0.84  % SZS output end Proof for theBenchmark
% 3.26/0.84  % (9136)------------------------------
% 3.26/0.84  % (9136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.84  % (9136)Termination reason: Refutation
% 3.26/0.84  
% 3.26/0.84  % (9136)Memory used [KB]: 9466
% 3.26/0.84  % (9136)Time elapsed: 0.442 s
% 3.26/0.84  % (9136)------------------------------
% 3.26/0.84  % (9136)------------------------------
% 3.26/0.85  % (9109)Success in time 0.491 s
%------------------------------------------------------------------------------
