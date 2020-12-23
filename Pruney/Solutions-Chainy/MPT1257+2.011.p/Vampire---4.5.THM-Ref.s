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
% DateTime   : Thu Dec  3 13:11:29 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 267 expanded)
%              Number of leaves         :   31 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  357 ( 656 expanded)
%              Number of equality atoms :   39 (  66 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f119,f147,f152,f271,f352,f357,f363,f384,f391,f396,f407,f430])).

fof(f430,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f422,f183])).

fof(f183,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f166,f78])).

fof(f78,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,X0) = X0
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f69,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f166,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))))
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f118,f118,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(f118,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl2_4
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f422,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(backward_demodulation,[],[f347,f418])).

fof(f418,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f412,f276])).

fof(f276,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f64,f270,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f270,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl2_7
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f412,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_14 ),
    inference(superposition,[],[f48,f406])).

fof(f406,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl2_14
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f347,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f344,f342])).

fof(f342,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f255,f341])).

fof(f341,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f273,f98])).

fof(f98,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f273,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f64,f270,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f255,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f250,f82])).

fof(f82,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f69,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f250,plain,
    ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f69,f151,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f151,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl2_6
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f344,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_2
    | spl2_3
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f118,f85,f76,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f76,plain,
    ( ! [X0] : ~ r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f74,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f74,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_3
  <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f85,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f81,f82])).

fof(f81,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f69,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f407,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f126,f67,f62,f404])).

fof(f126,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f396,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f378,f354,f67,f62,f393])).

fof(f393,plain,
    ( spl2_13
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f354,plain,
    ( spl2_9
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f378,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f64,f69,f69,f356,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f356,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f354])).

fof(f391,plain,
    ( spl2_12
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f101,f67,f62,f388])).

fof(f388,plain,
    ( spl2_12
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f101,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f44])).

fof(f384,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f98,f67,f62,f381])).

fof(f381,plain,
    ( spl2_11
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f363,plain,
    ( spl2_10
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f113,f67,f360])).

fof(f360,plain,
    ( spl2_10
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f113,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f103,f78])).

fof(f103,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK1)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f69,f69,f49])).

fof(f357,plain,
    ( spl2_9
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f329,f268,f67,f354])).

fof(f329,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f328,f79])).

fof(f79,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f69,f48])).

fof(f328,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f287,f78])).

fof(f287,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f270,f270,f49])).

fof(f352,plain,
    ( spl2_8
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f79,f67,f349])).

fof(f349,plain,
    ( spl2_8
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f271,plain,
    ( spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f77,f67,f268])).

fof(f77,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f69,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f152,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f96,f67,f62,f149])).

fof(f96,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f147,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f87,f67,f62,f144])).

fof(f144,plain,
    ( spl2_5
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f87,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f54])).

fof(f119,plain,
    ( spl2_4
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f86,f67,f62,f116])).

fof(f86,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f64,f69,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f75,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f41,f72])).

fof(f41,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

fof(f70,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f67])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f42,f62])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (15027)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.48  % (15035)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.48  % (15028)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (15040)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (15033)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (15028)Refutation not found, incomplete strategy% (15028)------------------------------
% 0.21/0.50  % (15028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15028)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15028)Memory used [KB]: 10490
% 0.21/0.50  % (15028)Time elapsed: 0.094 s
% 0.21/0.50  % (15028)------------------------------
% 0.21/0.50  % (15028)------------------------------
% 0.21/0.51  % (15029)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (15049)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (15026)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (15049)Refutation not found, incomplete strategy% (15049)------------------------------
% 0.21/0.51  % (15049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15049)Memory used [KB]: 10618
% 0.21/0.51  % (15049)Time elapsed: 0.096 s
% 0.21/0.51  % (15049)------------------------------
% 0.21/0.51  % (15049)------------------------------
% 0.21/0.51  % (15041)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (15044)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (15025)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.52  % (15038)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (15037)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (15039)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.53  % (15030)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.53  % (15045)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.53  % (15032)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (15042)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.53  % (15043)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (15031)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.54  % (15047)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.54  % (15046)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.54  % (15034)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.54  % (15036)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.87/0.60  % (15040)Refutation found. Thanks to Tanya!
% 1.87/0.60  % SZS status Theorem for theBenchmark
% 1.87/0.60  % SZS output start Proof for theBenchmark
% 1.87/0.60  fof(f431,plain,(
% 1.87/0.60    $false),
% 1.87/0.60    inference(avatar_sat_refutation,[],[f65,f70,f75,f119,f147,f152,f271,f352,f357,f363,f384,f391,f396,f407,f430])).
% 1.87/0.60  fof(f430,plain,(
% 1.87/0.60    ~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_14),
% 1.87/0.60    inference(avatar_contradiction_clause,[],[f429])).
% 1.87/0.60  fof(f429,plain,(
% 1.87/0.60    $false | (~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_14)),
% 1.87/0.60    inference(subsumption_resolution,[],[f422,f183])).
% 1.87/0.61  fof(f183,plain,(
% 1.87/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_4)),
% 1.87/0.61    inference(forward_demodulation,[],[f166,f78])).
% 1.87/0.61  fof(f78,plain,(
% 1.87/0.61    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,X0) = X0) ) | ~spl2_2),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f69,f56])).
% 1.87/0.61  fof(f56,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f36])).
% 1.87/0.61  fof(f36,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f4])).
% 1.87/0.61  fof(f4,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 1.87/0.61  fof(f69,plain,(
% 1.87/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.87/0.61    inference(avatar_component_clause,[],[f67])).
% 1.87/0.61  fof(f67,plain,(
% 1.87/0.61    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.87/0.61  fof(f166,plain,(
% 1.87/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))) | ~spl2_4),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f118,f118,f49])).
% 1.87/0.61  fof(f49,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f27])).
% 1.87/0.61  fof(f27,plain,(
% 1.87/0.61    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f9])).
% 1.87/0.61  fof(f9,axiom,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).
% 1.87/0.61  fof(f118,plain,(
% 1.87/0.61    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 1.87/0.61    inference(avatar_component_clause,[],[f116])).
% 1.87/0.61  fof(f116,plain,(
% 1.87/0.61    spl2_4 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.87/0.61  fof(f422,plain,(
% 1.87/0.61    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_7 | ~spl2_14)),
% 1.87/0.61    inference(backward_demodulation,[],[f347,f418])).
% 1.87/0.61  fof(f418,plain,(
% 1.87/0.61    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_7 | ~spl2_14)),
% 1.87/0.61    inference(subsumption_resolution,[],[f412,f276])).
% 1.87/0.61  fof(f276,plain,(
% 1.87/0.61    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_7)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f64,f270,f54])).
% 1.87/0.61  fof(f54,plain,(
% 1.87/0.61    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f33])).
% 1.87/0.61  fof(f33,plain,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.87/0.61    inference(flattening,[],[f32])).
% 1.87/0.61  fof(f32,plain,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f10])).
% 1.87/0.61  fof(f10,axiom,(
% 1.87/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.87/0.61  fof(f270,plain,(
% 1.87/0.61    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 1.87/0.61    inference(avatar_component_clause,[],[f268])).
% 1.87/0.61  fof(f268,plain,(
% 1.87/0.61    spl2_7 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.87/0.61  fof(f64,plain,(
% 1.87/0.61    l1_pre_topc(sK0) | ~spl2_1),
% 1.87/0.61    inference(avatar_component_clause,[],[f62])).
% 1.87/0.61  fof(f62,plain,(
% 1.87/0.61    spl2_1 <=> l1_pre_topc(sK0)),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.87/0.61  fof(f412,plain,(
% 1.87/0.61    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_14),
% 1.87/0.61    inference(superposition,[],[f48,f406])).
% 1.87/0.61  fof(f406,plain,(
% 1.87/0.61    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_14),
% 1.87/0.61    inference(avatar_component_clause,[],[f404])).
% 1.87/0.61  fof(f404,plain,(
% 1.87/0.61    spl2_14 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.87/0.61  fof(f48,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f26])).
% 1.87/0.61  fof(f26,plain,(
% 1.87/0.61    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f5])).
% 1.87/0.61  fof(f5,axiom,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.87/0.61  fof(f347,plain,(
% 1.87/0.61    ~r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_7)),
% 1.87/0.61    inference(forward_demodulation,[],[f344,f342])).
% 1.87/0.61  fof(f342,plain,(
% 1.87/0.61    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_1 | ~spl2_2 | ~spl2_6 | ~spl2_7)),
% 1.87/0.61    inference(backward_demodulation,[],[f255,f341])).
% 1.87/0.61  fof(f341,plain,(
% 1.87/0.61    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_7)),
% 1.87/0.61    inference(forward_demodulation,[],[f273,f98])).
% 1.87/0.61  fof(f98,plain,(
% 1.87/0.61    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_2)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f64,f69,f43])).
% 1.87/0.61  fof(f43,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f20])).
% 1.87/0.61  fof(f20,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f15])).
% 1.87/0.61  fof(f15,axiom,(
% 1.87/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 1.87/0.61  fof(f273,plain,(
% 1.87/0.61    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_1 | ~spl2_7)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f64,f270,f44])).
% 1.87/0.61  fof(f44,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f21])).
% 1.87/0.61  fof(f21,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f16])).
% 1.87/0.61  fof(f16,axiom,(
% 1.87/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.87/0.61  fof(f255,plain,(
% 1.87/0.61    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | (~spl2_2 | ~spl2_6)),
% 1.87/0.61    inference(forward_demodulation,[],[f250,f82])).
% 1.87/0.61  fof(f82,plain,(
% 1.87/0.61    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_2),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f69,f58])).
% 1.87/0.61  fof(f58,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f38])).
% 1.87/0.61  fof(f38,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f6])).
% 1.87/0.61  fof(f6,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.87/0.61  fof(f250,plain,(
% 1.87/0.61    k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_6)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f69,f151,f50])).
% 1.87/0.61  fof(f50,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f28])).
% 1.87/0.61  fof(f28,plain,(
% 1.87/0.61    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f8])).
% 1.87/0.61  fof(f8,axiom,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 1.87/0.61  fof(f151,plain,(
% 1.87/0.61    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 1.87/0.61    inference(avatar_component_clause,[],[f149])).
% 1.87/0.61  fof(f149,plain,(
% 1.87/0.61    spl2_6 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.87/0.61  fof(f344,plain,(
% 1.87/0.61    ~r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_2 | spl2_3 | ~spl2_4)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f118,f85,f76,f51])).
% 1.87/0.61  fof(f51,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f29])).
% 1.87/0.61  fof(f29,plain,(
% 1.87/0.61    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f7])).
% 1.87/0.61  fof(f7,axiom,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 1.87/0.61  fof(f76,plain,(
% 1.87/0.61    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(X0,k2_tops_1(sK0,sK1)))) ) | spl2_3),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f74,f60])).
% 1.87/0.61  fof(f60,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f39])).
% 1.87/0.61  fof(f39,plain,(
% 1.87/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.87/0.61    inference(ennf_transformation,[],[f1])).
% 1.87/0.61  fof(f1,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.87/0.61  fof(f74,plain,(
% 1.87/0.61    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | spl2_3),
% 1.87/0.61    inference(avatar_component_clause,[],[f72])).
% 1.87/0.61  fof(f72,plain,(
% 1.87/0.61    spl2_3 <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.87/0.61  fof(f85,plain,(
% 1.87/0.61    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_2),
% 1.87/0.61    inference(backward_demodulation,[],[f81,f82])).
% 1.87/0.61  fof(f81,plain,(
% 1.87/0.61    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_2),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f69,f57])).
% 1.87/0.61  fof(f57,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f37])).
% 1.87/0.61  fof(f37,plain,(
% 1.87/0.61    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f3])).
% 1.87/0.61  fof(f3,axiom,(
% 1.87/0.61    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 1.87/0.61  fof(f407,plain,(
% 1.87/0.61    spl2_14 | ~spl2_1 | ~spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f126,f67,f62,f404])).
% 1.87/0.61  fof(f126,plain,(
% 1.87/0.61    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_1 | ~spl2_2)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f64,f69,f45])).
% 1.87/0.61  fof(f45,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f22])).
% 1.87/0.61  fof(f22,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f12])).
% 1.87/0.61  fof(f12,axiom,(
% 1.87/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.87/0.61  fof(f396,plain,(
% 1.87/0.61    spl2_13 | ~spl2_1 | ~spl2_2 | ~spl2_9),
% 1.87/0.61    inference(avatar_split_clause,[],[f378,f354,f67,f62,f393])).
% 1.87/0.61  fof(f393,plain,(
% 1.87/0.61    spl2_13 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.87/0.61  fof(f354,plain,(
% 1.87/0.61    spl2_9 <=> r1_tarski(sK1,sK1)),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.87/0.61  fof(f378,plain,(
% 1.87/0.61    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl2_1 | ~spl2_2 | ~spl2_9)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f64,f69,f69,f356,f46])).
% 1.87/0.61  fof(f46,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f24])).
% 1.87/0.61  fof(f24,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.87/0.61    inference(flattening,[],[f23])).
% 1.87/0.61  fof(f23,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f11])).
% 1.87/0.61  fof(f11,axiom,(
% 1.87/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 1.87/0.61  fof(f356,plain,(
% 1.87/0.61    r1_tarski(sK1,sK1) | ~spl2_9),
% 1.87/0.61    inference(avatar_component_clause,[],[f354])).
% 1.87/0.61  fof(f391,plain,(
% 1.87/0.61    spl2_12 | ~spl2_1 | ~spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f101,f67,f62,f388])).
% 1.87/0.61  fof(f388,plain,(
% 1.87/0.61    spl2_12 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.87/0.61  fof(f101,plain,(
% 1.87/0.61    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_2)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f64,f69,f44])).
% 1.87/0.61  fof(f384,plain,(
% 1.87/0.61    spl2_11 | ~spl2_1 | ~spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f98,f67,f62,f381])).
% 1.87/0.61  fof(f381,plain,(
% 1.87/0.61    spl2_11 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.87/0.61  fof(f363,plain,(
% 1.87/0.61    spl2_10 | ~spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f113,f67,f360])).
% 1.87/0.61  fof(f360,plain,(
% 1.87/0.61    spl2_10 <=> r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.87/0.61  fof(f113,plain,(
% 1.87/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_2),
% 1.87/0.61    inference(forward_demodulation,[],[f103,f78])).
% 1.87/0.61  fof(f103,plain,(
% 1.87/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK1))) | ~spl2_2),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f69,f69,f49])).
% 1.87/0.61  fof(f357,plain,(
% 1.87/0.61    spl2_9 | ~spl2_2 | ~spl2_7),
% 1.87/0.61    inference(avatar_split_clause,[],[f329,f268,f67,f354])).
% 1.87/0.61  fof(f329,plain,(
% 1.87/0.61    r1_tarski(sK1,sK1) | (~spl2_2 | ~spl2_7)),
% 1.87/0.61    inference(forward_demodulation,[],[f328,f79])).
% 1.87/0.61  fof(f79,plain,(
% 1.87/0.61    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_2),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f69,f48])).
% 1.87/0.61  fof(f328,plain,(
% 1.87/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_7)),
% 1.87/0.61    inference(forward_demodulation,[],[f287,f78])).
% 1.87/0.61  fof(f287,plain,(
% 1.87/0.61    r1_tarski(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_7),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f270,f270,f49])).
% 1.87/0.61  fof(f352,plain,(
% 1.87/0.61    spl2_8 | ~spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f79,f67,f349])).
% 1.87/0.61  fof(f349,plain,(
% 1.87/0.61    spl2_8 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.87/0.61  fof(f271,plain,(
% 1.87/0.61    spl2_7 | ~spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f77,f67,f268])).
% 1.87/0.61  fof(f77,plain,(
% 1.87/0.61    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f69,f47])).
% 1.87/0.61  fof(f47,plain,(
% 1.87/0.61    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f25])).
% 1.87/0.61  fof(f25,plain,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f2])).
% 1.87/0.61  fof(f2,axiom,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.87/0.61  fof(f152,plain,(
% 1.87/0.61    spl2_6 | ~spl2_1 | ~spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f96,f67,f62,f149])).
% 1.87/0.61  fof(f96,plain,(
% 1.87/0.61    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_2)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f64,f69,f55])).
% 1.87/0.61  fof(f55,plain,(
% 1.87/0.61    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f35])).
% 1.87/0.61  fof(f35,plain,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.87/0.61    inference(flattening,[],[f34])).
% 1.87/0.61  fof(f34,plain,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f14])).
% 1.87/0.61  fof(f14,axiom,(
% 1.87/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.87/0.61  fof(f147,plain,(
% 1.87/0.61    spl2_5 | ~spl2_1 | ~spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f87,f67,f62,f144])).
% 1.87/0.61  fof(f144,plain,(
% 1.87/0.61    spl2_5 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.87/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.87/0.61  fof(f87,plain,(
% 1.87/0.61    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_2)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f64,f69,f54])).
% 1.87/0.61  fof(f119,plain,(
% 1.87/0.61    spl2_4 | ~spl2_1 | ~spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f86,f67,f62,f116])).
% 1.87/0.61  fof(f86,plain,(
% 1.87/0.61    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_2)),
% 1.87/0.61    inference(unit_resulting_resolution,[],[f64,f69,f53])).
% 1.87/0.61  fof(f53,plain,(
% 1.87/0.61    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f31])).
% 1.87/0.61  fof(f31,plain,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.87/0.61    inference(flattening,[],[f30])).
% 1.87/0.61  fof(f30,plain,(
% 1.87/0.61    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f13])).
% 1.87/0.61  fof(f13,axiom,(
% 1.87/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.87/0.61  fof(f75,plain,(
% 1.87/0.61    ~spl2_3),
% 1.87/0.61    inference(avatar_split_clause,[],[f41,f72])).
% 1.87/0.61  fof(f41,plain,(
% 1.87/0.61    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.87/0.61    inference(cnf_transformation,[],[f19])).
% 1.87/0.61  fof(f19,plain,(
% 1.87/0.61    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f18])).
% 1.87/0.61  fof(f18,negated_conjecture,(
% 1.87/0.61    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 1.87/0.61    inference(negated_conjecture,[],[f17])).
% 1.87/0.61  fof(f17,conjecture,(
% 1.87/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 1.87/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).
% 1.87/0.61  fof(f70,plain,(
% 1.87/0.61    spl2_2),
% 1.87/0.61    inference(avatar_split_clause,[],[f40,f67])).
% 1.87/0.61  fof(f40,plain,(
% 1.87/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.87/0.61    inference(cnf_transformation,[],[f19])).
% 1.87/0.61  fof(f65,plain,(
% 1.87/0.61    spl2_1),
% 1.87/0.61    inference(avatar_split_clause,[],[f42,f62])).
% 1.87/0.61  fof(f42,plain,(
% 1.87/0.61    l1_pre_topc(sK0)),
% 1.87/0.61    inference(cnf_transformation,[],[f19])).
% 1.87/0.61  % SZS output end Proof for theBenchmark
% 1.87/0.61  % (15040)------------------------------
% 1.87/0.61  % (15040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (15040)Termination reason: Refutation
% 1.87/0.61  
% 1.87/0.61  % (15040)Memory used [KB]: 1918
% 1.87/0.61  % (15040)Time elapsed: 0.194 s
% 1.87/0.61  % (15040)------------------------------
% 1.87/0.61  % (15040)------------------------------
% 1.87/0.61  % (15023)Success in time 0.242 s
%------------------------------------------------------------------------------
