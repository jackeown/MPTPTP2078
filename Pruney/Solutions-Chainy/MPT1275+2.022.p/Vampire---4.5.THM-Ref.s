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
% DateTime   : Thu Dec  3 13:12:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 410 expanded)
%              Number of leaves         :   30 ( 141 expanded)
%              Depth                    :   17
%              Number of atoms          :  463 (1110 expanded)
%              Number of equality atoms :   92 ( 261 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f369,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f104,f106,f154,f235,f240,f247,f257,f261,f327,f333,f337,f368])).

fof(f368,plain,
    ( ~ spl2_3
    | spl2_6
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl2_3
    | spl2_6
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f366,f102])).

fof(f102,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl2_6
  <=> sK1 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f366,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f365,f226])).

fof(f226,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f223,f205])).

fof(f205,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f129,f194])).

fof(f194,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f193,f132])).

fof(f132,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(X2,X2),X2) ),
    inference(resolution,[],[f124,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f124,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f123,f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f50,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f123,plain,(
    ! [X0] :
      ( m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f60,f120])).

fof(f120,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f61,f87])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f193,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(X0,X0),X0)
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f63,f191])).

fof(f191,plain,(
    ! [X1] : k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(forward_demodulation,[],[f187,f129])).

fof(f187,plain,(
    ! [X1] : k3_subset_1(X1,k4_xboole_0(X1,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X1)) ),
    inference(resolution,[],[f121,f132])).

fof(f121,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) ) ),
    inference(resolution,[],[f61,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f129,plain,(
    ! [X0] : k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f126,f120])).

fof(f126,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f62,f87])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f223,plain,(
    ! [X3] : k3_subset_1(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(resolution,[],[f207,f61])).

fof(f207,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f124,f194])).

fof(f365,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_11
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f364,f153])).

fof(f153,plain,
    ( ! [X10] : k7_subset_1(u1_struct_0(sK0),sK1,X10) = k4_xboole_0(sK1,X10)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl2_11
  <=> ! [X10] : k7_subset_1(u1_struct_0(sK0),sK1,X10) = k4_xboole_0(sK1,X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f364,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_21
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f350,f332])).

fof(f332,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl2_21
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f350,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_17
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f349,f246])).

fof(f246,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl2_17
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f349,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_22 ),
    inference(resolution,[],[f336,f85])).

fof(f85,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f336,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl2_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f337,plain,
    ( spl2_22
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f167,f73,f335])).

fof(f73,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f333,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f268,f254,f83,f73,f330])).

fof(f254,plain,
    ( spl2_18
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f268,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f267,f75])).

fof(f267,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_18 ),
    inference(subsumption_resolution,[],[f264,f85])).

fof(f264,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_18 ),
    inference(resolution,[],[f256,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f256,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f254])).

fof(f327,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_5
    | ~ spl2_18 ),
    inference(unit_resulting_resolution,[],[f75,f80,f256,f85,f98,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

fof(f98,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_5
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f80,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f261,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f260,f97,f83,f73,f254])).

fof(f260,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f259,f75])).

fof(f259,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f258,f85])).

fof(f258,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f99,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f99,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f257,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f252,f238,f101,f83,f254])).

fof(f238,plain,
    ( spl2_16
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f252,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f251,f85])).

fof(f251,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(sK1,sK0)
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f249,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f249,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(sK1,sK0)
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(superposition,[],[f239,f103])).

fof(f103,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f238])).

fof(f247,plain,
    ( spl2_17
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f242,f233,f83,f78,f244])).

fof(f233,plain,
    ( spl2_15
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f242,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f241,f85])).

fof(f241,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_15 ),
    inference(resolution,[],[f234,f80])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f233])).

fof(f240,plain,
    ( spl2_16
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f155,f73,f238])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f59,f75])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f235,plain,
    ( spl2_15
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f140,f73,f233])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_1 ),
    inference(resolution,[],[f52,f75])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f154,plain,
    ( spl2_11
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f137,f83,f152])).

fof(f137,plain,
    ( ! [X10] : k7_subset_1(u1_struct_0(sK0),sK1,X10) = k4_xboole_0(sK1,X10)
    | ~ spl2_3 ),
    inference(resolution,[],[f69,f85])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f106,plain,
    ( ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f105,f101,f97])).

fof(f105,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f48,f103])).

fof(f48,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f104,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f47,f101,f97])).

fof(f47,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f83])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f46,f78])).

fof(f46,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f44,f73])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (5519)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.46  % (5519)Refutation not found, incomplete strategy% (5519)------------------------------
% 0.21/0.46  % (5519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (5519)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (5519)Memory used [KB]: 1663
% 0.21/0.46  % (5519)Time elapsed: 0.067 s
% 0.21/0.46  % (5519)------------------------------
% 0.21/0.46  % (5519)------------------------------
% 0.21/0.46  % (5514)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (5514)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (5526)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (5534)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (5517)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (5516)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (5517)Refutation not found, incomplete strategy% (5517)------------------------------
% 0.21/0.50  % (5517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5517)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5517)Memory used [KB]: 6140
% 0.21/0.50  % (5517)Time elapsed: 0.095 s
% 0.21/0.50  % (5517)------------------------------
% 0.21/0.50  % (5517)------------------------------
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f76,f81,f86,f104,f106,f154,f235,f240,f247,f257,f261,f327,f333,f337,f368])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    ~spl2_3 | spl2_6 | ~spl2_11 | ~spl2_17 | ~spl2_21 | ~spl2_22),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f367])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    $false | (~spl2_3 | spl2_6 | ~spl2_11 | ~spl2_17 | ~spl2_21 | ~spl2_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f366,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    sK1 != k2_tops_1(sK0,sK1) | spl2_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl2_6 <=> sK1 = k2_tops_1(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    sK1 = k2_tops_1(sK0,sK1) | (~spl2_3 | ~spl2_11 | ~spl2_17 | ~spl2_21 | ~spl2_22)),
% 0.21/0.50    inference(forward_demodulation,[],[f365,f226])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 0.21/0.50    inference(forward_demodulation,[],[f223,f205])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(backward_demodulation,[],[f129,f194])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f193,f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X2] : (r1_tarski(k4_xboole_0(X2,X2),X2)) )),
% 0.21/0.50    inference(resolution,[],[f124,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f123,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f50,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(superposition,[],[f60,f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ( ! [X0] : (k3_subset_1(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f61,f87])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,X0),X0) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(superposition,[],[f63,f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 0.21/0.50    inference(forward_demodulation,[],[f187,f129])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X1] : (k3_subset_1(X1,k4_xboole_0(X1,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X1))) )),
% 0.21/0.50    inference(resolution,[],[f121,f132])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)) )),
% 0.21/0.50    inference(resolution,[],[f61,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X0] : (k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.50    inference(forward_demodulation,[],[f126,f120])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 0.21/0.50    inference(resolution,[],[f62,f87])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X3] : (k3_subset_1(X3,k1_xboole_0) = k4_xboole_0(X3,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f207,f61])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f124,f194])).
% 0.21/0.50  fof(f365,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) | (~spl2_3 | ~spl2_11 | ~spl2_17 | ~spl2_21 | ~spl2_22)),
% 0.21/0.50    inference(forward_demodulation,[],[f364,f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ( ! [X10] : (k7_subset_1(u1_struct_0(sK0),sK1,X10) = k4_xboole_0(sK1,X10)) ) | ~spl2_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl2_11 <=> ! [X10] : k7_subset_1(u1_struct_0(sK0),sK1,X10) = k4_xboole_0(sK1,X10)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.50  fof(f364,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | (~spl2_3 | ~spl2_17 | ~spl2_21 | ~spl2_22)),
% 0.21/0.50    inference(forward_demodulation,[],[f350,f332])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f330])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    spl2_21 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.50  fof(f350,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_17 | ~spl2_22)),
% 0.21/0.50    inference(forward_demodulation,[],[f349,f246])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f244])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    spl2_17 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_22)),
% 0.21/0.50    inference(resolution,[],[f336,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f335])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    spl2_22 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    spl2_22 | ~spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f167,f73,f335])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl2_1 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_1),
% 0.21/0.50    inference(resolution,[],[f51,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    l1_pre_topc(sK0) | ~spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    spl2_21 | ~spl2_1 | ~spl2_3 | ~spl2_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f268,f254,f83,f73,f330])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    spl2_18 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_1 | ~spl2_3 | ~spl2_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f267,f75])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f264,f85])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_18),
% 0.21/0.50    inference(resolution,[],[f256,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    v2_tops_1(sK1,sK0) | ~spl2_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f254])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f326])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_5 | ~spl2_18)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f75,f80,f256,f85,f98,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ~v3_tops_1(sK1,sK0) | spl2_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl2_5 <=> v3_tops_1(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    v4_pre_topc(sK1,sK0) | ~spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl2_2 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    spl2_18 | ~spl2_1 | ~spl2_3 | ~spl2_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f260,f97,f83,f73,f254])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    v2_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3 | ~spl2_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f259,f75])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f258,f85])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_5),
% 0.21/0.50    inference(resolution,[],[f99,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_tops_1(X1,X0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    v3_tops_1(sK1,sK0) | ~spl2_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    spl2_18 | ~spl2_3 | ~spl2_6 | ~spl2_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f252,f238,f101,f83,f254])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    spl2_16 <=> ! [X0] : (~r1_tarski(X0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    v2_tops_1(sK1,sK0) | (~spl2_3 | ~spl2_6 | ~spl2_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f251,f85])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0) | (~spl2_6 | ~spl2_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f249,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ~r1_tarski(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0) | (~spl2_6 | ~spl2_16)),
% 0.21/0.50    inference(superposition,[],[f239,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    sK1 = k2_tops_1(sK0,sK1) | ~spl2_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | ~spl2_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f238])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    spl2_17 | ~spl2_2 | ~spl2_3 | ~spl2_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f242,f233,f83,f78,f244])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    spl2_15 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_15)),
% 0.21/0.50    inference(subsumption_resolution,[],[f241,f85])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_15)),
% 0.21/0.50    inference(resolution,[],[f234,f80])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f233])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    spl2_16 | ~spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f155,f73,f238])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | ~spl2_1),
% 0.21/0.50    inference(resolution,[],[f59,f75])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl2_15 | ~spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f140,f73,f233])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_1),
% 0.21/0.50    inference(resolution,[],[f52,f75])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl2_11 | ~spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f137,f83,f152])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X10] : (k7_subset_1(u1_struct_0(sK0),sK1,X10) = k4_xboole_0(sK1,X10)) ) | ~spl2_3),
% 0.21/0.50    inference(resolution,[],[f69,f85])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ~spl2_5 | ~spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f105,f101,f97])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ~v3_tops_1(sK1,sK0) | ~spl2_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f48,f103])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f37,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f16])).
% 0.21/0.50  fof(f16,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl2_5 | spl2_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f101,f97])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f83])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f78])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v4_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f73])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (5514)------------------------------
% 0.21/0.50  % (5514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5514)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (5514)Memory used [KB]: 6396
% 0.21/0.50  % (5514)Time elapsed: 0.085 s
% 0.21/0.50  % (5514)------------------------------
% 0.21/0.50  % (5514)------------------------------
% 0.21/0.50  % (5503)Success in time 0.144 s
%------------------------------------------------------------------------------
