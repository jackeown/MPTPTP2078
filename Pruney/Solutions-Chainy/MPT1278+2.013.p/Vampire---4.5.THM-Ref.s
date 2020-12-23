%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 269 expanded)
%              Number of leaves         :   32 ( 114 expanded)
%              Depth                    :   13
%              Number of atoms          :  475 ( 877 expanded)
%              Number of equality atoms :   75 ( 153 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f94,f99,f107,f112,f145,f151,f159,f164,f171,f175,f192,f209,f266,f272,f328])).

fof(f328,plain,
    ( ~ spl2_2
    | spl2_5
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_17
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl2_2
    | spl2_5
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_17
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f326,f87])).

fof(f87,plain,
    ( k1_xboole_0 != sK1
    | spl2_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f326,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_17
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f316,f113])).

fof(f113,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f61,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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

fof(f316,plain,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_17
    | ~ spl2_24
    | ~ spl2_25 ),
    inference(backward_demodulation,[],[f265,f309])).

fof(f309,plain,
    ( k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f234,f271])).

fof(f271,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl2_25
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f234,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f233,f158])).

fof(f158,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl2_12
  <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f233,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f232,f106])).

fof(f106,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl2_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f232,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_17 ),
    inference(subsumption_resolution,[],[f228,f72])).

fof(f72,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f228,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_17 ),
    inference(resolution,[],[f208,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f208,plain,
    ( v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl2_17
  <=> v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f265,plain,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl2_24
  <=> sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f272,plain,
    ( spl2_25
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f226,f189,f156,f104,f70,f269])).

fof(f189,plain,
    ( spl2_16
  <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f226,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f225,f158])).

fof(f225,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_8
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f224,f106])).

fof(f224,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f223,f72])).

fof(f223,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_16 ),
    inference(resolution,[],[f191,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f191,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f189])).

fof(f266,plain,
    ( spl2_24
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f204,f161,f142,f109,f263])).

fof(f109,plain,
    ( spl2_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f142,plain,
    ( spl2_10
  <=> k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f161,plain,
    ( spl2_13
  <=> sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f204,plain,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f203,f163])).

fof(f163,plain,
    ( sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f203,plain,
    ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f197,f144])).

fof(f144,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f197,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_9 ),
    inference(resolution,[],[f119,f111])).

fof(f111,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f119,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k4_xboole_0(X1,k3_subset_1(X1,X2)) = k3_subset_1(X1,k3_subset_1(X1,X2)) ) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f209,plain,
    ( spl2_17
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f185,f173,f161,f156,f75,f206])).

fof(f75,plain,
    ( spl2_3
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f173,plain,
    ( spl2_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f185,plain,
    ( v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f184,f158])).

fof(f184,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_3
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f180,f77])).

fof(f77,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f180,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_13
    | ~ spl2_15 ),
    inference(superposition,[],[f174,f163])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f192,plain,
    ( spl2_16
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f178,f169,f142,f109,f80,f189])).

fof(f80,plain,
    ( spl2_4
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f169,plain,
    ( spl2_14
  <=> ! [X0] :
        ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f178,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f177,f144])).

fof(f177,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_4
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f176,f111])).

fof(f176,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_4
    | ~ spl2_14 ),
    inference(resolution,[],[f170,f82])).

fof(f82,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v3_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f175,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f137,f104,f70,f173])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f136,f106])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f135,f106])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f53,f72])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f171,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f130,f104,f70,f169])).

fof(f130,plain,
    ( ! [X0] :
        ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_tops_1(X0,sK0) )
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f129,f106])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_tops_1(X0,sK0)
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f128,f106])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ v3_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f49,f72])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(f164,plain,
    ( spl2_13
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f154,f148,f142,f161])).

fof(f148,plain,
    ( spl2_11
  <=> sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f154,plain,
    ( sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f150,f144])).

fof(f150,plain,
    ( sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f159,plain,
    ( spl2_12
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f153,f142,f109,f156])).

fof(f153,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f152,f111])).

fof(f152,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(superposition,[],[f54,f144])).

fof(f151,plain,
    ( spl2_11
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f122,f109,f148])).

fof(f122,plain,
    ( sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_9 ),
    inference(resolution,[],[f56,f111])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f145,plain,
    ( spl2_10
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f118,f109,f142])).

fof(f118,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)
    | ~ spl2_9 ),
    inference(resolution,[],[f55,f111])).

fof(f112,plain,
    ( spl2_9
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f102,f96,f91,f109])).

fof(f91,plain,
    ( spl2_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f96,plain,
    ( spl2_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f102,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f98,f101])).

fof(f101,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f45,f93])).

fof(f93,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f107,plain,
    ( spl2_8
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f101,f91,f104])).

fof(f99,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & v3_tops_1(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK1
      & v3_tops_1(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f94,plain,
    ( spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f89,f70,f91])).

fof(f89,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f46,f72])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f88,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f42,f85])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f41,f80])).

fof(f41,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f40,f75])).

fof(f40,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f38,f70])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:26:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (3696)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (3704)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (3696)Refutation not found, incomplete strategy% (3696)------------------------------
% 0.21/0.50  % (3696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3696)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3696)Memory used [KB]: 10618
% 0.21/0.50  % (3696)Time elapsed: 0.071 s
% 0.21/0.50  % (3696)------------------------------
% 0.21/0.50  % (3696)------------------------------
% 0.21/0.50  % (3692)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (3692)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f94,f99,f107,f112,f145,f151,f159,f164,f171,f175,f192,f209,f266,f272,f328])).
% 0.21/0.51  fof(f328,plain,(
% 0.21/0.51    ~spl2_2 | spl2_5 | ~spl2_8 | ~spl2_12 | ~spl2_17 | ~spl2_24 | ~spl2_25),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f327])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    $false | (~spl2_2 | spl2_5 | ~spl2_8 | ~spl2_12 | ~spl2_17 | ~spl2_24 | ~spl2_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f326,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl2_5 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | (~spl2_2 | ~spl2_8 | ~spl2_12 | ~spl2_17 | ~spl2_24 | ~spl2_25)),
% 0.21/0.51    inference(forward_demodulation,[],[f316,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(resolution,[],[f61,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.51    inference(nnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    sK1 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_2 | ~spl2_8 | ~spl2_12 | ~spl2_17 | ~spl2_24 | ~spl2_25)),
% 0.21/0.51    inference(backward_demodulation,[],[f265,f309])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),sK1) | (~spl2_2 | ~spl2_8 | ~spl2_12 | ~spl2_17 | ~spl2_25)),
% 0.21/0.51    inference(forward_demodulation,[],[f234,f271])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f269])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    spl2_25 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_8 | ~spl2_12 | ~spl2_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f233,f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl2_12 <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_8 | ~spl2_17)),
% 0.21/0.51    inference(forward_demodulation,[],[f232,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl2_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_17)),
% 0.21/0.51    inference(subsumption_resolution,[],[f228,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    k4_xboole_0(k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_17),
% 0.21/0.51    inference(resolution,[],[f208,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f206])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    spl2_17 <=> v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f263])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    spl2_24 <=> sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    spl2_25 | ~spl2_2 | ~spl2_8 | ~spl2_12 | ~spl2_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f226,f189,f156,f104,f70,f269])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    spl2_16 <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_8 | ~spl2_12 | ~spl2_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f225,f158])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_8 | ~spl2_16)),
% 0.21/0.51    inference(forward_demodulation,[],[f224,f106])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f223,f72])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_16),
% 0.21/0.51    inference(resolution,[],[f191,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f189])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl2_24 | ~spl2_9 | ~spl2_10 | ~spl2_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f204,f161,f142,f109,f263])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl2_9 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl2_10 <=> k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl2_13 <=> sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_9 | ~spl2_10 | ~spl2_13)),
% 0.21/0.51    inference(forward_demodulation,[],[f203,f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f161])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_9 | ~spl2_10)),
% 0.21/0.51    inference(forward_demodulation,[],[f197,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) | ~spl2_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl2_9),
% 0.21/0.51    inference(resolution,[],[f119,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k4_xboole_0(X1,k3_subset_1(X1,X2)) = k3_subset_1(X1,k3_subset_1(X1,X2))) )),
% 0.21/0.51    inference(resolution,[],[f55,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    spl2_17 | ~spl2_3 | ~spl2_12 | ~spl2_13 | ~spl2_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f185,f173,f161,f156,f75,f206])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl2_3 <=> v3_pre_topc(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    spl2_15 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl2_3 | ~spl2_12 | ~spl2_13 | ~spl2_15)),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f158])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl2_3 | ~spl2_13 | ~spl2_15)),
% 0.21/0.51    inference(subsumption_resolution,[],[f180,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK0) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl2_13 | ~spl2_15)),
% 0.21/0.51    inference(superposition,[],[f174,f163])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl2_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f173])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    spl2_16 | ~spl2_4 | ~spl2_9 | ~spl2_10 | ~spl2_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f178,f169,f142,f109,f80,f189])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl2_4 <=> v3_tops_1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl2_14 <=> ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_tops_1(X0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | (~spl2_4 | ~spl2_9 | ~spl2_10 | ~spl2_14)),
% 0.21/0.51    inference(forward_demodulation,[],[f177,f144])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (~spl2_4 | ~spl2_9 | ~spl2_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f176,f111])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (~spl2_4 | ~spl2_14)),
% 0.21/0.51    inference(resolution,[],[f170,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    v3_tops_1(sK1,sK0) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)) ) | ~spl2_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    spl2_15 | ~spl2_2 | ~spl2_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f137,f104,f70,f173])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) ) | (~spl2_2 | ~spl2_8)),
% 0.21/0.51    inference(forward_demodulation,[],[f136,f106])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl2_2 | ~spl2_8)),
% 0.21/0.51    inference(forward_demodulation,[],[f135,f106])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl2_2),
% 0.21/0.51    inference(resolution,[],[f53,f72])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl2_14 | ~spl2_2 | ~spl2_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f130,f104,f70,f169])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ( ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_tops_1(X0,sK0)) ) | (~spl2_2 | ~spl2_8)),
% 0.21/0.51    inference(forward_demodulation,[],[f129,f106])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_tops_1(X0,sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)) ) | (~spl2_2 | ~spl2_8)),
% 0.21/0.51    inference(forward_demodulation,[],[f128,f106])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X0] : (~v3_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)) ) | ~spl2_2),
% 0.21/0.51    inference(resolution,[],[f49,f72])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl2_13 | ~spl2_10 | ~spl2_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f154,f148,f142,f161])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl2_11 <=> sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_10 | ~spl2_11)),
% 0.21/0.51    inference(forward_demodulation,[],[f150,f144])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl2_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f148])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl2_12 | ~spl2_9 | ~spl2_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f153,f142,f109,f156])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_9 | ~spl2_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f152,f111])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_10),
% 0.21/0.51    inference(superposition,[],[f54,f144])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl2_11 | ~spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f122,f109,f148])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl2_9),
% 0.21/0.51    inference(resolution,[],[f56,f111])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl2_10 | ~spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f118,f109,f142])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) | ~spl2_9),
% 0.21/0.51    inference(resolution,[],[f55,f111])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl2_9 | ~spl2_6 | ~spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f102,f96,f91,f109])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl2_6 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl2_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_6 | ~spl2_7)),
% 0.21/0.51    inference(backward_demodulation,[],[f98,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_6),
% 0.21/0.51    inference(resolution,[],[f45,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl2_8 | ~spl2_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f101,f91,f104])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f96])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f14])).
% 0.21/0.51  fof(f14,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl2_6 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f89,f70,f91])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl2_2),
% 0.21/0.51    inference(resolution,[],[f46,f72])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f85])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f80])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v3_tops_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f75])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f70])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (3692)------------------------------
% 0.21/0.51  % (3692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3692)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (3692)Memory used [KB]: 6268
% 0.21/0.51  % (3692)Time elapsed: 0.092 s
% 0.21/0.51  % (3692)------------------------------
% 0.21/0.51  % (3692)------------------------------
% 0.21/0.51  % (3689)Success in time 0.14 s
%------------------------------------------------------------------------------
