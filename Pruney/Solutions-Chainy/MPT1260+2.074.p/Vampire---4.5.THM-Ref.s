%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:45 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 330 expanded)
%              Number of leaves         :   38 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  475 ( 869 expanded)
%              Number of equality atoms :   73 ( 185 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1014,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f95,f135,f140,f394,f416,f560,f597,f706,f757,f769,f783,f793,f804,f820,f826,f875,f979,f1008])).

fof(f1008,plain,
    ( ~ spl3_7
    | ~ spl3_49
    | spl3_11
    | ~ spl3_65 ),
    inference(avatar_split_clause,[],[f996,f975,f215,f779,f130])).

fof(f130,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f779,plain,
    ( spl3_49
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f215,plain,
    ( spl3_11
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f975,plain,
    ( spl3_65
  <=> sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f996,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_65 ),
    inference(superposition,[],[f195,f977])).

fof(f977,plain,
    ( sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f975])).

fof(f195,plain,(
    ! [X6,X7] :
      ( k1_tops_1(X6,X7) = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,k2_tops_1(X6,X7))))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X6,X7] :
      ( k1_tops_1(X6,X7) = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,k2_tops_1(X6,X7))))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6) ) ),
    inference(superposition,[],[f82,f52])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f74,f77])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f61,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f979,plain,
    ( ~ spl3_24
    | spl3_65
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f953,f744,f975,f578])).

fof(f578,plain,
    ( spl3_24
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f744,plain,
    ( spl3_46
  <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f953,plain,
    ( sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_46 ),
    inference(superposition,[],[f82,f746])).

fof(f746,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f744])).

fof(f875,plain,
    ( ~ spl3_24
    | ~ spl3_37
    | spl3_46
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f868,f582,f744,f703,f578])).

fof(f703,plain,
    ( spl3_37
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f582,plain,
    ( spl3_25
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f868,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_25 ),
    inference(superposition,[],[f507,f584])).

fof(f584,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f582])).

fof(f507,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,X1,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f489])).

fof(f489,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,X1,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f235,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f235,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X1,X0) = k7_subset_1(X1,k3_subset_1(X1,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ) ),
    inference(condensation,[],[f234])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f73,f65])).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f826,plain,(
    spl3_49 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | spl3_49 ),
    inference(subsumption_resolution,[],[f48,f781])).

fof(f781,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f779])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f820,plain,
    ( ~ spl3_24
    | ~ spl3_8
    | spl3_25
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f811,f91,f582,f160,f578])).

fof(f160,plain,
    ( spl3_8
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f91,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f811,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_2 ),
    inference(superposition,[],[f151,f92])).

fof(f92,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f151,plain,(
    ! [X6,X4,X5] :
      ( k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    inference(superposition,[],[f82,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f804,plain,(
    spl3_47 ),
    inference(avatar_contradiction_clause,[],[f801])).

fof(f801,plain,
    ( $false
    | spl3_47 ),
    inference(subsumption_resolution,[],[f96,f751])).

fof(f751,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f749])).

fof(f749,plain,
    ( spl3_47
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f96,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f72,f48])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f793,plain,
    ( ~ spl3_47
    | ~ spl3_7
    | ~ spl3_6
    | spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f777,f215,f87,f126,f130,f749])).

fof(f126,plain,
    ( spl3_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f87,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f777,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_11 ),
    inference(superposition,[],[f117,f217])).

fof(f217,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f215])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f66,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f783,plain,
    ( ~ spl3_7
    | ~ spl3_49
    | spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f774,f215,f91,f779,f130])).

fof(f774,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_11 ),
    inference(superposition,[],[f53,f217])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f769,plain,(
    spl3_48 ),
    inference(avatar_contradiction_clause,[],[f766])).

fof(f766,plain,
    ( $false
    | spl3_48 ),
    inference(unit_resulting_resolution,[],[f84,f755])).

fof(f755,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_48 ),
    inference(avatar_component_clause,[],[f753])).

fof(f753,plain,
    ( spl3_48
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f757,plain,
    ( spl3_11
    | ~ spl3_7
    | ~ spl3_47
    | ~ spl3_1
    | ~ spl3_48
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f447,f414,f753,f87,f749,f130,f215])).

fof(f414,plain,
    ( spl3_16
  <=> ! [X17] :
        ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X17,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X17,sK1)
        | ~ v3_pre_topc(X17,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f447,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_16 ),
    inference(duplicate_literal_removal,[],[f443])).

fof(f443,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_16 ),
    inference(resolution,[],[f419,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_tops_1(X0,X1))
      | ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = X1 ) ),
    inference(resolution,[],[f201,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f201,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f196,f71])).

fof(f196,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | r1_tarski(k1_tops_1(X4,X5),X5)
      | ~ l1_pre_topc(X4) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X4,X5] :
      ( r1_tarski(k1_tops_1(X4,X5),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4) ) ),
    inference(superposition,[],[f154,f52])).

fof(f154,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k7_subset_1(X8,X6,X7),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X8)) ) ),
    inference(superposition,[],[f80,f82])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f419,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_16 ),
    inference(resolution,[],[f415,f71])).

fof(f415,plain,
    ( ! [X17] :
        ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X17,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X17,sK1)
        | ~ v3_pre_topc(X17,sK0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f414])).

fof(f706,plain,
    ( ~ spl3_24
    | spl3_37
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f688,f582,f703,f578])).

fof(f688,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_25 ),
    inference(superposition,[],[f62,f584])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f597,plain,
    ( ~ spl3_13
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | ~ spl3_13
    | spl3_24 ),
    inference(unit_resulting_resolution,[],[f393,f580,f71])).

fof(f580,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f578])).

fof(f393,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl3_13
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f560,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f50,f48,f172,f554])).

fof(f554,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f552])).

fof(f552,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f171,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_pre_topc(X0,X1),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f147,f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f75,f72])).

fof(f75,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f172,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | spl3_8 ),
    inference(resolution,[],[f162,f71])).

fof(f162,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f160])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f416,plain,
    ( ~ spl3_7
    | spl3_16 ),
    inference(avatar_split_clause,[],[f410,f414,f130])).

fof(f410,plain,(
    ! [X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v3_pre_topc(X17,sK0)
      | ~ r1_tarski(X17,sK1)
      | r1_tarski(X17,k1_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f394,plain,
    ( ~ spl3_7
    | spl3_13 ),
    inference(avatar_split_clause,[],[f387,f391,f130])).

fof(f387,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f381,f48])).

fof(f381,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(X0,k2_pre_topc(X1,X0))
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f379])).

fof(f379,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_pre_topc(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f359,f67])).

fof(f359,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f356])).

fof(f356,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f352,f51])).

fof(f352,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_subset_1(X2,X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f79,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f76,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) ),
    inference(definition_unfolding,[],[f57,f78])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f140,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f50,f132])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f135,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f49,f128])).

fof(f128,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f46,f91,f87])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f47,f91,f87])).

fof(f47,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (9782)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (9779)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (9777)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (9804)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (9796)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.56  % (9805)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.57  % (9789)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.57  % (9794)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.57  % (9776)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.58  % (9781)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.58  % (9780)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.59  % (9783)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.59  % (9788)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.59  % (9778)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.60  % (9799)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.61  % (9791)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.61  % (9797)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.61  % (9795)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.79/0.61  % (9784)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.79/0.62  % (9792)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.79/0.62  % (9802)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.79/0.62  % (9785)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.79/0.62  % (9798)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.79/0.62  % (9803)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.79/0.62  % (9790)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.79/0.62  % (9800)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.79/0.62  % (9793)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.79/0.62  % (9801)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.79/0.63  % (9787)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.12/0.64  % (9789)Refutation found. Thanks to Tanya!
% 2.12/0.64  % SZS status Theorem for theBenchmark
% 2.12/0.64  % (9792)Refutation not found, incomplete strategy% (9792)------------------------------
% 2.12/0.64  % (9792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.64  % (9792)Termination reason: Refutation not found, incomplete strategy
% 2.12/0.64  
% 2.12/0.64  % (9792)Memory used [KB]: 10746
% 2.12/0.64  % (9792)Time elapsed: 0.207 s
% 2.12/0.64  % (9792)------------------------------
% 2.12/0.64  % (9792)------------------------------
% 2.12/0.64  % (9786)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.12/0.65  % SZS output start Proof for theBenchmark
% 2.12/0.65  fof(f1014,plain,(
% 2.12/0.65    $false),
% 2.12/0.65    inference(avatar_sat_refutation,[],[f94,f95,f135,f140,f394,f416,f560,f597,f706,f757,f769,f783,f793,f804,f820,f826,f875,f979,f1008])).
% 2.12/0.65  fof(f1008,plain,(
% 2.12/0.65    ~spl3_7 | ~spl3_49 | spl3_11 | ~spl3_65),
% 2.12/0.65    inference(avatar_split_clause,[],[f996,f975,f215,f779,f130])).
% 2.12/0.65  fof(f130,plain,(
% 2.12/0.65    spl3_7 <=> l1_pre_topc(sK0)),
% 2.12/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.12/0.65  fof(f779,plain,(
% 2.12/0.65    spl3_49 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.12/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 2.12/0.65  fof(f215,plain,(
% 2.12/0.65    spl3_11 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.12/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.12/0.65  fof(f975,plain,(
% 2.12/0.65    spl3_65 <=> sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))),
% 2.12/0.65    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 2.12/0.65  fof(f996,plain,(
% 2.12/0.65    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_65),
% 2.12/0.65    inference(superposition,[],[f195,f977])).
% 2.12/0.65  fof(f977,plain,(
% 2.12/0.65    sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~spl3_65),
% 2.12/0.65    inference(avatar_component_clause,[],[f975])).
% 2.12/0.65  fof(f195,plain,(
% 2.12/0.65    ( ! [X6,X7] : (k1_tops_1(X6,X7) = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,k2_tops_1(X6,X7)))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~l1_pre_topc(X6)) )),
% 2.12/0.65    inference(duplicate_literal_removal,[],[f194])).
% 2.12/0.65  fof(f194,plain,(
% 2.12/0.65    ( ! [X6,X7] : (k1_tops_1(X6,X7) = k5_xboole_0(X7,k1_setfam_1(k2_tarski(X7,k2_tops_1(X6,X7)))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~l1_pre_topc(X6)) )),
% 2.12/0.65    inference(superposition,[],[f82,f52])).
% 2.12/0.65  fof(f52,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f28])).
% 2.12/0.65  fof(f28,plain,(
% 2.12/0.65    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.12/0.65    inference(ennf_transformation,[],[f22])).
% 2.12/0.65  fof(f22,axiom,(
% 2.12/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.12/0.65  fof(f82,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.12/0.65    inference(definition_unfolding,[],[f74,f77])).
% 2.12/0.65  fof(f77,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.12/0.65    inference(definition_unfolding,[],[f61,f59])).
% 2.12/0.65  fof(f59,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f15])).
% 2.12/0.65  fof(f15,axiom,(
% 2.12/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.12/0.65  fof(f61,plain,(
% 2.12/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f2])).
% 2.12/0.65  fof(f2,axiom,(
% 2.12/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.12/0.66  fof(f74,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f41])).
% 2.12/0.66  fof(f41,plain,(
% 2.12/0.66    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.12/0.66    inference(ennf_transformation,[],[f13])).
% 2.12/0.66  fof(f13,axiom,(
% 2.12/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.12/0.66  fof(f979,plain,(
% 2.12/0.66    ~spl3_24 | spl3_65 | ~spl3_46),
% 2.12/0.66    inference(avatar_split_clause,[],[f953,f744,f975,f578])).
% 2.12/0.66  fof(f578,plain,(
% 2.12/0.66    spl3_24 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.12/0.66  fof(f744,plain,(
% 2.12/0.66    spl3_46 <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 2.12/0.66  fof(f953,plain,(
% 2.12/0.66    sK1 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_46),
% 2.12/0.66    inference(superposition,[],[f82,f746])).
% 2.12/0.66  fof(f746,plain,(
% 2.12/0.66    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~spl3_46),
% 2.12/0.66    inference(avatar_component_clause,[],[f744])).
% 2.12/0.66  fof(f875,plain,(
% 2.12/0.66    ~spl3_24 | ~spl3_37 | spl3_46 | ~spl3_25),
% 2.12/0.66    inference(avatar_split_clause,[],[f868,f582,f744,f703,f578])).
% 2.12/0.66  fof(f703,plain,(
% 2.12/0.66    spl3_37 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.12/0.66  fof(f582,plain,(
% 2.12/0.66    spl3_25 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.12/0.66  fof(f868,plain,(
% 2.12/0.66    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_25),
% 2.12/0.66    inference(superposition,[],[f507,f584])).
% 2.28/0.66  fof(f584,plain,(
% 2.28/0.66    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl3_25),
% 2.28/0.66    inference(avatar_component_clause,[],[f582])).
% 2.28/0.66  fof(f507,plain,(
% 2.28/0.66    ( ! [X0,X1] : (k7_subset_1(X0,X1,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(duplicate_literal_removal,[],[f489])).
% 2.28/0.66  fof(f489,plain,(
% 2.28/0.66    ( ! [X0,X1] : (k7_subset_1(X0,X1,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(superposition,[],[f235,f64])).
% 2.28/0.66  fof(f64,plain,(
% 2.28/0.66    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(cnf_transformation,[],[f34])).
% 2.28/0.66  fof(f34,plain,(
% 2.28/0.66    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.66    inference(ennf_transformation,[],[f10])).
% 2.28/0.66  fof(f10,axiom,(
% 2.28/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.28/0.66  fof(f235,plain,(
% 2.28/0.66    ( ! [X0,X1] : (k3_subset_1(X1,X0) = k7_subset_1(X1,k3_subset_1(X1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1))) )),
% 2.28/0.66    inference(condensation,[],[f234])).
% 2.28/0.66  fof(f234,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,k3_subset_1(X0,X1),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(superposition,[],[f73,f65])).
% 2.28/0.66  fof(f65,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(cnf_transformation,[],[f35])).
% 2.28/0.66  fof(f35,plain,(
% 2.28/0.66    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.66    inference(ennf_transformation,[],[f14])).
% 2.28/0.66  fof(f14,axiom,(
% 2.28/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 2.28/0.66  fof(f73,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(cnf_transformation,[],[f40])).
% 2.28/0.66  fof(f40,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.28/0.66    inference(ennf_transformation,[],[f9])).
% 2.28/0.66  fof(f9,axiom,(
% 2.28/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 2.28/0.66  fof(f826,plain,(
% 2.28/0.66    spl3_49),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f822])).
% 2.28/0.66  fof(f822,plain,(
% 2.28/0.66    $false | spl3_49),
% 2.28/0.66    inference(subsumption_resolution,[],[f48,f781])).
% 2.28/0.66  fof(f781,plain,(
% 2.28/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_49),
% 2.28/0.66    inference(avatar_component_clause,[],[f779])).
% 2.28/0.66  fof(f48,plain,(
% 2.28/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.28/0.66    inference(cnf_transformation,[],[f26])).
% 2.28/0.66  fof(f26,plain,(
% 2.28/0.66    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.28/0.66    inference(flattening,[],[f25])).
% 2.28/0.66  fof(f25,plain,(
% 2.28/0.66    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.28/0.66    inference(ennf_transformation,[],[f24])).
% 2.28/0.66  fof(f24,negated_conjecture,(
% 2.28/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.28/0.66    inference(negated_conjecture,[],[f23])).
% 2.28/0.66  fof(f23,conjecture,(
% 2.28/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 2.28/0.66  fof(f820,plain,(
% 2.28/0.66    ~spl3_24 | ~spl3_8 | spl3_25 | ~spl3_2),
% 2.28/0.66    inference(avatar_split_clause,[],[f811,f91,f582,f160,f578])).
% 2.28/0.66  fof(f160,plain,(
% 2.28/0.66    spl3_8 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.28/0.66  fof(f91,plain,(
% 2.28/0.66    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.28/0.66  fof(f811,plain,(
% 2.28/0.66    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_2),
% 2.28/0.66    inference(superposition,[],[f151,f92])).
% 2.28/0.66  fof(f92,plain,(
% 2.28/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 2.28/0.66    inference(avatar_component_clause,[],[f91])).
% 2.28/0.66  fof(f151,plain,(
% 2.28/0.66    ( ! [X6,X4,X5] : (k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(X6)) | ~m1_subset_1(X5,k1_zfmisc_1(X4))) )),
% 2.28/0.66    inference(superposition,[],[f82,f81])).
% 2.28/0.66  fof(f81,plain,(
% 2.28/0.66    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(definition_unfolding,[],[f63,f77])).
% 2.28/0.66  fof(f63,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f33])).
% 2.28/0.66  fof(f33,plain,(
% 2.28/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.66    inference(ennf_transformation,[],[f6])).
% 2.28/0.66  fof(f6,axiom,(
% 2.28/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.28/0.66  fof(f804,plain,(
% 2.28/0.66    spl3_47),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f801])).
% 2.28/0.66  fof(f801,plain,(
% 2.28/0.66    $false | spl3_47),
% 2.28/0.66    inference(subsumption_resolution,[],[f96,f751])).
% 2.28/0.66  fof(f751,plain,(
% 2.28/0.66    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_47),
% 2.28/0.66    inference(avatar_component_clause,[],[f749])).
% 2.28/0.66  fof(f749,plain,(
% 2.28/0.66    spl3_47 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 2.28/0.66  fof(f96,plain,(
% 2.28/0.66    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.28/0.66    inference(resolution,[],[f72,f48])).
% 2.28/0.66  fof(f72,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f16])).
% 2.28/0.66  fof(f16,axiom,(
% 2.28/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.28/0.66  fof(f793,plain,(
% 2.28/0.66    ~spl3_47 | ~spl3_7 | ~spl3_6 | spl3_1 | ~spl3_11),
% 2.28/0.66    inference(avatar_split_clause,[],[f777,f215,f87,f126,f130,f749])).
% 2.28/0.66  fof(f126,plain,(
% 2.28/0.66    spl3_6 <=> v2_pre_topc(sK0)),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.28/0.66  fof(f87,plain,(
% 2.28/0.66    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.28/0.66  fof(f777,plain,(
% 2.28/0.66    v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_11),
% 2.28/0.66    inference(superposition,[],[f117,f217])).
% 2.28/0.66  fof(f217,plain,(
% 2.28/0.66    sK1 = k1_tops_1(sK0,sK1) | ~spl3_11),
% 2.28/0.66    inference(avatar_component_clause,[],[f215])).
% 2.28/0.66  fof(f117,plain,(
% 2.28/0.66    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r1_tarski(X1,u1_struct_0(X0))) )),
% 2.28/0.66    inference(resolution,[],[f66,f71])).
% 2.28/0.66  fof(f71,plain,(
% 2.28/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f16])).
% 2.28/0.66  fof(f66,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f37])).
% 2.28/0.66  fof(f37,plain,(
% 2.28/0.66    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.28/0.66    inference(flattening,[],[f36])).
% 2.28/0.66  fof(f36,plain,(
% 2.28/0.66    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.28/0.66    inference(ennf_transformation,[],[f18])).
% 2.28/0.66  fof(f18,axiom,(
% 2.28/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.28/0.66  fof(f783,plain,(
% 2.28/0.66    ~spl3_7 | ~spl3_49 | spl3_2 | ~spl3_11),
% 2.28/0.66    inference(avatar_split_clause,[],[f774,f215,f91,f779,f130])).
% 2.28/0.66  fof(f774,plain,(
% 2.28/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_11),
% 2.28/0.66    inference(superposition,[],[f53,f217])).
% 2.28/0.66  fof(f53,plain,(
% 2.28/0.66    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f29])).
% 2.28/0.66  fof(f29,plain,(
% 2.28/0.66    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.28/0.66    inference(ennf_transformation,[],[f19])).
% 2.28/0.66  fof(f19,axiom,(
% 2.28/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.28/0.66  fof(f769,plain,(
% 2.28/0.66    spl3_48),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f766])).
% 2.28/0.66  fof(f766,plain,(
% 2.28/0.66    $false | spl3_48),
% 2.28/0.66    inference(unit_resulting_resolution,[],[f84,f755])).
% 2.28/0.66  fof(f755,plain,(
% 2.28/0.66    ~r1_tarski(sK1,sK1) | spl3_48),
% 2.28/0.66    inference(avatar_component_clause,[],[f753])).
% 2.28/0.66  fof(f753,plain,(
% 2.28/0.66    spl3_48 <=> r1_tarski(sK1,sK1)),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 2.28/0.66  fof(f84,plain,(
% 2.28/0.66    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.28/0.66    inference(equality_resolution,[],[f69])).
% 2.28/0.66  fof(f69,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.28/0.66    inference(cnf_transformation,[],[f1])).
% 2.28/0.66  fof(f1,axiom,(
% 2.28/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.28/0.66  fof(f757,plain,(
% 2.28/0.66    spl3_11 | ~spl3_7 | ~spl3_47 | ~spl3_1 | ~spl3_48 | ~spl3_16),
% 2.28/0.66    inference(avatar_split_clause,[],[f447,f414,f753,f87,f749,f130,f215])).
% 2.28/0.66  fof(f414,plain,(
% 2.28/0.66    spl3_16 <=> ! [X17] : (~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X17,k1_tops_1(sK0,sK1)) | ~r1_tarski(X17,sK1) | ~v3_pre_topc(X17,sK0))),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.28/0.66  fof(f447,plain,(
% 2.28/0.66    ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,sK1) | ~spl3_16),
% 2.28/0.66    inference(duplicate_literal_removal,[],[f443])).
% 2.28/0.66  fof(f443,plain,(
% 2.28/0.66    ~r1_tarski(sK1,sK1) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,u1_struct_0(sK0)) | ~r1_tarski(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,sK1) | ~spl3_16),
% 2.28/0.66    inference(resolution,[],[f419,f223])).
% 2.28/0.66  fof(f223,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~r1_tarski(X1,k1_tops_1(X0,X1)) | ~r1_tarski(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = X1) )),
% 2.28/0.66    inference(resolution,[],[f201,f70])).
% 2.28/0.66  fof(f70,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.28/0.66    inference(cnf_transformation,[],[f1])).
% 2.28/0.66  fof(f201,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0) | ~r1_tarski(X1,u1_struct_0(X0))) )),
% 2.28/0.66    inference(resolution,[],[f196,f71])).
% 2.28/0.66  fof(f196,plain,(
% 2.28/0.66    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | r1_tarski(k1_tops_1(X4,X5),X5) | ~l1_pre_topc(X4)) )),
% 2.28/0.66    inference(duplicate_literal_removal,[],[f193])).
% 2.28/0.66  fof(f193,plain,(
% 2.28/0.66    ( ! [X4,X5] : (r1_tarski(k1_tops_1(X4,X5),X5) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4)) )),
% 2.28/0.66    inference(superposition,[],[f154,f52])).
% 2.28/0.66  fof(f154,plain,(
% 2.28/0.66    ( ! [X6,X8,X7] : (r1_tarski(k7_subset_1(X8,X6,X7),X6) | ~m1_subset_1(X6,k1_zfmisc_1(X8))) )),
% 2.28/0.66    inference(superposition,[],[f80,f82])).
% 2.28/0.66  fof(f80,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.28/0.66    inference(definition_unfolding,[],[f58,f77])).
% 2.28/0.66  fof(f58,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f3])).
% 2.28/0.66  fof(f3,axiom,(
% 2.28/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.28/0.66  fof(f419,plain,(
% 2.28/0.66    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl3_16),
% 2.28/0.66    inference(resolution,[],[f415,f71])).
% 2.28/0.66  fof(f415,plain,(
% 2.28/0.66    ( ! [X17] : (~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X17,k1_tops_1(sK0,sK1)) | ~r1_tarski(X17,sK1) | ~v3_pre_topc(X17,sK0)) ) | ~spl3_16),
% 2.28/0.66    inference(avatar_component_clause,[],[f414])).
% 2.28/0.66  fof(f706,plain,(
% 2.28/0.66    ~spl3_24 | spl3_37 | ~spl3_25),
% 2.28/0.66    inference(avatar_split_clause,[],[f688,f582,f703,f578])).
% 2.28/0.66  fof(f688,plain,(
% 2.28/0.66    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_25),
% 2.28/0.66    inference(superposition,[],[f62,f584])).
% 2.28/0.66  fof(f62,plain,(
% 2.28/0.66    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(cnf_transformation,[],[f32])).
% 2.28/0.66  fof(f32,plain,(
% 2.28/0.66    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.66    inference(ennf_transformation,[],[f7])).
% 2.28/0.66  fof(f7,axiom,(
% 2.28/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.28/0.66  fof(f597,plain,(
% 2.28/0.66    ~spl3_13 | spl3_24),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f595])).
% 2.28/0.66  fof(f595,plain,(
% 2.28/0.66    $false | (~spl3_13 | spl3_24)),
% 2.28/0.66    inference(unit_resulting_resolution,[],[f393,f580,f71])).
% 2.28/0.66  fof(f580,plain,(
% 2.28/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_24),
% 2.28/0.66    inference(avatar_component_clause,[],[f578])).
% 2.28/0.66  fof(f393,plain,(
% 2.28/0.66    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_13),
% 2.28/0.66    inference(avatar_component_clause,[],[f391])).
% 2.28/0.66  fof(f391,plain,(
% 2.28/0.66    spl3_13 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.28/0.66    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.28/0.66  fof(f560,plain,(
% 2.28/0.66    spl3_8),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f555])).
% 2.28/0.66  fof(f555,plain,(
% 2.28/0.66    $false | spl3_8),
% 2.28/0.66    inference(unit_resulting_resolution,[],[f50,f48,f172,f554])).
% 2.28/0.66  fof(f554,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 2.28/0.66    inference(duplicate_literal_removal,[],[f552])).
% 2.28/0.66  fof(f552,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 2.28/0.66    inference(resolution,[],[f171,f67])).
% 2.28/0.66  fof(f67,plain,(
% 2.28/0.66    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f39])).
% 2.28/0.66  fof(f39,plain,(
% 2.28/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.28/0.66    inference(flattening,[],[f38])).
% 2.28/0.66  fof(f38,plain,(
% 2.28/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.28/0.66    inference(ennf_transformation,[],[f17])).
% 2.28/0.66  fof(f17,axiom,(
% 2.28/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.28/0.66  fof(f171,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,X1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 2.28/0.66    inference(duplicate_literal_removal,[],[f168])).
% 2.28/0.66  fof(f168,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.28/0.66    inference(superposition,[],[f147,f51])).
% 2.28/0.66  fof(f51,plain,(
% 2.28/0.66    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f27])).
% 2.28/0.66  fof(f27,plain,(
% 2.28/0.66    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.28/0.66    inference(ennf_transformation,[],[f21])).
% 2.28/0.66  fof(f21,axiom,(
% 2.28/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.28/0.66  fof(f147,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (r1_tarski(k4_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.28/0.66    inference(resolution,[],[f75,f72])).
% 2.28/0.66  fof(f75,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(cnf_transformation,[],[f43])).
% 2.28/0.66  fof(f43,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.66    inference(flattening,[],[f42])).
% 2.28/0.66  fof(f42,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.28/0.66    inference(ennf_transformation,[],[f8])).
% 2.28/0.66  fof(f8,axiom,(
% 2.28/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.28/0.66  fof(f172,plain,(
% 2.28/0.66    ~r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) | spl3_8),
% 2.28/0.66    inference(resolution,[],[f162,f71])).
% 2.28/0.66  fof(f162,plain,(
% 2.28/0.66    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 2.28/0.66    inference(avatar_component_clause,[],[f160])).
% 2.28/0.66  fof(f50,plain,(
% 2.28/0.66    l1_pre_topc(sK0)),
% 2.28/0.66    inference(cnf_transformation,[],[f26])).
% 2.28/0.66  fof(f416,plain,(
% 2.28/0.66    ~spl3_7 | spl3_16),
% 2.28/0.66    inference(avatar_split_clause,[],[f410,f414,f130])).
% 2.28/0.66  fof(f410,plain,(
% 2.28/0.66    ( ! [X17] : (~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_pre_topc(X17,sK0) | ~r1_tarski(X17,sK1) | r1_tarski(X17,k1_tops_1(sK0,sK1))) )),
% 2.28/0.66    inference(resolution,[],[f54,f48])).
% 2.28/0.66  fof(f54,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 2.28/0.66    inference(cnf_transformation,[],[f31])).
% 2.28/0.66  fof(f31,plain,(
% 2.28/0.66    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.28/0.66    inference(flattening,[],[f30])).
% 2.28/0.66  fof(f30,plain,(
% 2.28/0.66    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.28/0.66    inference(ennf_transformation,[],[f20])).
% 2.28/0.66  fof(f20,axiom,(
% 2.28/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 2.28/0.66  fof(f394,plain,(
% 2.28/0.66    ~spl3_7 | spl3_13),
% 2.28/0.66    inference(avatar_split_clause,[],[f387,f391,f130])).
% 2.28/0.66  fof(f387,plain,(
% 2.28/0.66    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.28/0.66    inference(resolution,[],[f381,f48])).
% 2.28/0.66  fof(f381,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(X0,k2_pre_topc(X1,X0)) | ~l1_pre_topc(X1)) )),
% 2.28/0.66    inference(duplicate_literal_removal,[],[f379])).
% 2.28/0.66  fof(f379,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_pre_topc(X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 2.28/0.66    inference(resolution,[],[f359,f67])).
% 2.28/0.66  fof(f359,plain,(
% 2.28/0.66    ( ! [X0,X1] : (~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.28/0.66    inference(duplicate_literal_removal,[],[f356])).
% 2.28/0.66  fof(f356,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.28/0.66    inference(superposition,[],[f352,f51])).
% 2.28/0.66  fof(f352,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_subset_1(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 2.28/0.66    inference(superposition,[],[f79,f83])).
% 2.28/0.66  fof(f83,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.28/0.66    inference(definition_unfolding,[],[f76,f78])).
% 2.28/0.66  fof(f78,plain,(
% 2.28/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 2.28/0.66    inference(definition_unfolding,[],[f60,f77])).
% 2.28/0.66  fof(f60,plain,(
% 2.28/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.28/0.66    inference(cnf_transformation,[],[f5])).
% 2.28/0.66  fof(f5,axiom,(
% 2.28/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.28/0.66  fof(f76,plain,(
% 2.28/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 2.28/0.66    inference(cnf_transformation,[],[f45])).
% 2.28/0.66  fof(f45,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.28/0.66    inference(flattening,[],[f44])).
% 2.28/0.66  fof(f44,plain,(
% 2.28/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.28/0.66    inference(ennf_transformation,[],[f12])).
% 2.28/0.66  fof(f12,axiom,(
% 2.28/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.28/0.66  fof(f79,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))))) )),
% 2.28/0.66    inference(definition_unfolding,[],[f57,f78])).
% 2.28/0.66  fof(f57,plain,(
% 2.28/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.28/0.66    inference(cnf_transformation,[],[f4])).
% 2.28/0.66  fof(f4,axiom,(
% 2.28/0.66    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.28/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.28/0.66  fof(f140,plain,(
% 2.28/0.66    spl3_7),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f139])).
% 2.28/0.66  fof(f139,plain,(
% 2.28/0.66    $false | spl3_7),
% 2.28/0.66    inference(subsumption_resolution,[],[f50,f132])).
% 2.28/0.66  fof(f132,plain,(
% 2.28/0.66    ~l1_pre_topc(sK0) | spl3_7),
% 2.28/0.66    inference(avatar_component_clause,[],[f130])).
% 2.28/0.66  fof(f135,plain,(
% 2.28/0.66    spl3_6),
% 2.28/0.66    inference(avatar_contradiction_clause,[],[f134])).
% 2.28/0.66  fof(f134,plain,(
% 2.28/0.66    $false | spl3_6),
% 2.28/0.66    inference(subsumption_resolution,[],[f49,f128])).
% 2.28/0.66  fof(f128,plain,(
% 2.28/0.66    ~v2_pre_topc(sK0) | spl3_6),
% 2.28/0.66    inference(avatar_component_clause,[],[f126])).
% 2.28/0.66  fof(f49,plain,(
% 2.28/0.66    v2_pre_topc(sK0)),
% 2.28/0.66    inference(cnf_transformation,[],[f26])).
% 2.28/0.66  fof(f95,plain,(
% 2.28/0.66    spl3_1 | spl3_2),
% 2.28/0.66    inference(avatar_split_clause,[],[f46,f91,f87])).
% 2.28/0.66  fof(f46,plain,(
% 2.28/0.66    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.28/0.66    inference(cnf_transformation,[],[f26])).
% 2.28/0.66  fof(f94,plain,(
% 2.28/0.66    ~spl3_1 | ~spl3_2),
% 2.28/0.66    inference(avatar_split_clause,[],[f47,f91,f87])).
% 2.28/0.66  fof(f47,plain,(
% 2.28/0.66    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.28/0.66    inference(cnf_transformation,[],[f26])).
% 2.28/0.66  % SZS output end Proof for theBenchmark
% 2.28/0.66  % (9789)------------------------------
% 2.28/0.66  % (9789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.66  % (9789)Termination reason: Refutation
% 2.28/0.66  
% 2.28/0.66  % (9789)Memory used [KB]: 6908
% 2.28/0.66  % (9789)Time elapsed: 0.203 s
% 2.28/0.66  % (9789)------------------------------
% 2.28/0.66  % (9789)------------------------------
% 2.28/0.66  % (9775)Success in time 0.301 s
%------------------------------------------------------------------------------
