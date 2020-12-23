%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 229 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :    8
%              Number of atoms          :  259 ( 578 expanded)
%              Number of equality atoms :   68 ( 135 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30535)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f1220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f55,f60,f65,f84,f140,f235,f262,f321,f885,f888,f899,f903,f922,f1000,f1001,f1208])).

fof(f1208,plain,(
    spl2_23 ),
    inference(avatar_contradiction_clause,[],[f1183])).

fof(f1183,plain,
    ( $false
    | spl2_23 ),
    inference(unit_resulting_resolution,[],[f391,f1173])).

fof(f1173,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f151,f89])).

fof(f89,plain,(
    ! [X2] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X2)) ),
    inference(superposition,[],[f44,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f36,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f151,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[],[f86,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f86,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f44,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f391,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | spl2_23 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl2_23
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f1001,plain,
    ( spl2_13
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f993,f144,f206])).

fof(f206,plain,
    ( spl2_13
  <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f144,plain,
    ( spl2_9
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f993,plain,
    ( k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_9 ),
    inference(superposition,[],[f78,f146])).

fof(f146,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f73,f37])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) ),
    inference(unit_resulting_resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1000,plain,
    ( spl2_10
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f999,f144,f80,f170])).

fof(f170,plain,
    ( spl2_10
  <=> sK1 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f80,plain,
    ( spl2_5
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f999,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f992,f82])).

fof(f82,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f992,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(superposition,[],[f44,f146])).

fof(f922,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f920,f137,f57,f144])).

fof(f57,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f137,plain,
    ( spl2_8
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f920,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(superposition,[],[f119,f139])).

fof(f139,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f119,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f59,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f59,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f903,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f902,f62,f57,f47,f123])).

fof(f123,plain,
    ( spl2_6
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f47,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f62,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f902,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f64,f59,f49,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f49,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f899,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_6 ),
    inference(avatar_split_clause,[],[f127,f123,f62,f57,f47])).

fof(f127,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f64,f59,f125,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f125,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f888,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) != k4_xboole_0(sK1,sK1)
    | k1_tops_1(sK0,sK1) != k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f885,plain,
    ( spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f881,f80,f51])).

fof(f51,plain,
    ( spl2_2
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f881,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(superposition,[],[f114,f82])).

fof(f114,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f91,f37])).

fof(f91,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k2_tarski(X2,X3)),X2) ),
    inference(superposition,[],[f36,f44])).

fof(f321,plain,
    ( spl2_5
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f320,f259,f80])).

fof(f259,plain,
    ( spl2_17
  <=> k1_xboole_0 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f320,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f316,f31])).

fof(f316,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_17 ),
    inference(superposition,[],[f44,f261])).

fof(f261,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f259])).

fof(f262,plain,
    ( spl2_17
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f247,f144,f123,f259])).

fof(f247,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f146,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f235,plain,
    ( spl2_14
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f229,f170,f232])).

fof(f232,plain,
    ( spl2_14
  <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f229,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(sK1,sK1)
    | ~ spl2_10 ),
    inference(superposition,[],[f44,f172])).

fof(f172,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f140,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f134,f62,f57,f137])).

fof(f134,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f64,f59,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f84,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f75,f51,f80])).

fof(f75,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f65,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
          | ~ v2_tops_1(X1,sK0) )
        & ( r1_tarski(X1,k2_tops_1(sK0,X1))
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | ~ v2_tops_1(sK1,sK0) )
      & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f60,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f29,f51,f47])).

fof(f29,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f30,f51,f47])).

fof(f30,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:21:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (30539)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (30537)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (30540)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (30538)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (30547)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (30542)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (30544)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (30550)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (30536)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.52  % (30545)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (30548)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.52  % (30546)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.54  % (30540)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (30551)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.57  % (30534)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  % (30535)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.57  fof(f1220,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f54,f55,f60,f65,f84,f140,f235,f262,f321,f885,f888,f899,f903,f922,f1000,f1001,f1208])).
% 0.22/0.57  fof(f1208,plain,(
% 0.22/0.57    spl2_23),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f1183])).
% 0.22/0.57  fof(f1183,plain,(
% 0.22/0.57    $false | spl2_23),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f391,f1173])).
% 0.22/0.57  fof(f1173,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.57    inference(forward_demodulation,[],[f151,f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    ( ! [X2] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X2))) )),
% 0.22/0.57    inference(superposition,[],[f44,f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f36,f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f39,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.57  fof(f151,plain,(
% 0.22/0.57    ( ! [X0] : (k4_xboole_0(X0,X0) = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 0.22/0.57    inference(superposition,[],[f86,f37])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.57  fof(f86,plain,(
% 0.22/0.57    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0)) )),
% 0.22/0.57    inference(superposition,[],[f44,f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.57  fof(f391,plain,(
% 0.22/0.57    k1_xboole_0 != k4_xboole_0(sK1,sK1) | spl2_23),
% 0.22/0.57    inference(avatar_component_clause,[],[f390])).
% 0.22/0.57  fof(f390,plain,(
% 0.22/0.57    spl2_23 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.57  fof(f1001,plain,(
% 0.22/0.57    spl2_13 | ~spl2_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f993,f144,f206])).
% 0.22/0.57  fof(f206,plain,(
% 0.22/0.57    spl2_13 <=> k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.57  fof(f144,plain,(
% 0.22/0.57    spl2_9 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.57  fof(f993,plain,(
% 0.22/0.57    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | ~spl2_9),
% 0.22/0.57    inference(superposition,[],[f78,f146])).
% 0.22/0.57  fof(f146,plain,(
% 0.22/0.57    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_9),
% 0.22/0.57    inference(avatar_component_clause,[],[f144])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.57    inference(forward_demodulation,[],[f73,f37])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0))) )),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f36,f45])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.22/0.57    inference(definition_unfolding,[],[f41,f38])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.57  fof(f1000,plain,(
% 0.22/0.57    spl2_10 | ~spl2_5 | ~spl2_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f999,f144,f80,f170])).
% 0.22/0.57  fof(f170,plain,(
% 0.22/0.57    spl2_10 <=> sK1 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.57  fof(f80,plain,(
% 0.22/0.57    spl2_5 <=> sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.57  fof(f999,plain,(
% 0.22/0.57    sK1 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl2_5 | ~spl2_9)),
% 0.22/0.57    inference(forward_demodulation,[],[f992,f82])).
% 0.22/0.57  fof(f82,plain,(
% 0.22/0.57    sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f80])).
% 0.22/0.57  fof(f992,plain,(
% 0.22/0.57    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_9),
% 0.22/0.57    inference(superposition,[],[f44,f146])).
% 0.22/0.57  fof(f922,plain,(
% 0.22/0.57    spl2_9 | ~spl2_3 | ~spl2_8),
% 0.22/0.57    inference(avatar_split_clause,[],[f920,f137,f57,f144])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    spl2_8 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.57  fof(f920,plain,(
% 0.22/0.57    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_8)),
% 0.22/0.57    inference(superposition,[],[f119,f139])).
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_8),
% 0.22/0.57    inference(avatar_component_clause,[],[f137])).
% 0.22/0.57  fof(f119,plain,(
% 0.22/0.57    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_3),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f59,f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f57])).
% 0.22/0.57  fof(f903,plain,(
% 0.22/0.57    ~spl2_6 | spl2_1 | ~spl2_3 | ~spl2_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f902,f62,f57,f47,f123])).
% 0.22/0.57  fof(f123,plain,(
% 0.22/0.57    spl2_6 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    spl2_4 <=> l1_pre_topc(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.57  fof(f902,plain,(
% 0.22/0.57    k1_xboole_0 != k1_tops_1(sK0,sK1) | (spl2_1 | ~spl2_3 | ~spl2_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f64,f59,f49,f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ~v2_tops_1(sK1,sK0) | spl2_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f47])).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    l1_pre_topc(sK0) | ~spl2_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f62])).
% 0.22/0.57  fof(f899,plain,(
% 0.22/0.57    ~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_6),
% 0.22/0.57    inference(avatar_split_clause,[],[f127,f123,f62,f57,f47])).
% 0.22/0.57  fof(f127,plain,(
% 0.22/0.57    ~v2_tops_1(sK1,sK0) | (~spl2_3 | ~spl2_4 | spl2_6)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f64,f59,f125,f33])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f125,plain,(
% 0.22/0.57    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f123])).
% 0.22/0.57  fof(f888,plain,(
% 0.22/0.57    k1_xboole_0 != k4_xboole_0(sK1,sK1) | k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) != k4_xboole_0(sK1,sK1) | k1_tops_1(sK0,sK1) != k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.22/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.57  fof(f885,plain,(
% 0.22/0.57    spl2_2 | ~spl2_5),
% 0.22/0.57    inference(avatar_split_clause,[],[f881,f80,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    spl2_2 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.57  fof(f881,plain,(
% 0.22/0.57    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl2_5),
% 0.22/0.57    inference(superposition,[],[f114,f82])).
% 0.22/0.57  fof(f114,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 0.22/0.57    inference(superposition,[],[f91,f37])).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k2_tarski(X2,X3)),X2)) )),
% 0.22/0.57    inference(superposition,[],[f36,f44])).
% 0.22/0.57  fof(f321,plain,(
% 0.22/0.57    spl2_5 | ~spl2_17),
% 0.22/0.57    inference(avatar_split_clause,[],[f320,f259,f80])).
% 0.22/0.57  fof(f259,plain,(
% 0.22/0.57    spl2_17 <=> k1_xboole_0 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.57  fof(f320,plain,(
% 0.22/0.57    sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_17),
% 0.22/0.57    inference(forward_demodulation,[],[f316,f31])).
% 0.22/0.57  fof(f316,plain,(
% 0.22/0.57    k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_xboole_0) | ~spl2_17),
% 0.22/0.57    inference(superposition,[],[f44,f261])).
% 0.22/0.57  fof(f261,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_17),
% 0.22/0.57    inference(avatar_component_clause,[],[f259])).
% 0.22/0.57  fof(f262,plain,(
% 0.22/0.57    spl2_17 | ~spl2_6 | ~spl2_9),
% 0.22/0.57    inference(avatar_split_clause,[],[f247,f144,f123,f259])).
% 0.22/0.57  fof(f247,plain,(
% 0.22/0.57    k1_xboole_0 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_6 | ~spl2_9)),
% 0.22/0.57    inference(backward_demodulation,[],[f146,f124])).
% 0.22/0.57  fof(f124,plain,(
% 0.22/0.57    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f123])).
% 0.22/0.57  fof(f235,plain,(
% 0.22/0.57    spl2_14 | ~spl2_10),
% 0.22/0.57    inference(avatar_split_clause,[],[f229,f170,f232])).
% 0.22/0.57  fof(f232,plain,(
% 0.22/0.57    spl2_14 <=> k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(sK1,sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.57  fof(f229,plain,(
% 0.22/0.57    k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(sK1,sK1) | ~spl2_10),
% 0.22/0.57    inference(superposition,[],[f44,f172])).
% 0.22/0.57  fof(f172,plain,(
% 0.22/0.57    sK1 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_10),
% 0.22/0.57    inference(avatar_component_clause,[],[f170])).
% 0.22/0.57  fof(f140,plain,(
% 0.22/0.57    spl2_8 | ~spl2_3 | ~spl2_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f134,f62,f57,f137])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f64,f59,f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,axiom,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.22/0.57  fof(f84,plain,(
% 0.22/0.57    spl2_5 | ~spl2_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f75,f51,f80])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    sK1 = k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 0.22/0.57    inference(resolution,[],[f45,f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f51])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    spl2_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f27,f62])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    l1_pre_topc(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f24,f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.57    inference(flattening,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,negated_conjecture,(
% 0.22/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.22/0.57    inference(negated_conjecture,[],[f13])).
% 0.22/0.57  fof(f13,conjecture,(
% 0.22/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    spl2_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f28,f57])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    spl2_1 | spl2_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f29,f51,f47])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ~spl2_1 | ~spl2_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f30,f51,f47])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (30540)------------------------------
% 0.22/0.57  % (30540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (30540)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (30540)Memory used [KB]: 6780
% 0.22/0.57  % (30540)Time elapsed: 0.117 s
% 0.22/0.57  % (30540)------------------------------
% 0.22/0.57  % (30540)------------------------------
% 0.22/0.57  % (30533)Success in time 0.209 s
%------------------------------------------------------------------------------
