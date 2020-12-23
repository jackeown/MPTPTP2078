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
% DateTime   : Thu Dec  3 13:21:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 521 expanded)
%              Number of leaves         :   21 ( 124 expanded)
%              Depth                    :   16
%              Number of atoms          :  328 (1910 expanded)
%              Number of equality atoms :   31 (  85 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f184,f218,f220,f304,f315,f319,f361,f380,f383])).

fof(f383,plain,
    ( ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f322,f379])).

fof(f379,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl3_10
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f322,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f144,f217])).

fof(f217,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_5
  <=> sK1 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f144,plain,(
    ~ v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f90,f143])).

fof(f143,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(global_subsumption,[],[f89,f142])).

fof(f142,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f89,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f74,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f74,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f90,plain,(
    ~ v1_subset_1(k2_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f74,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f380,plain,
    ( ~ spl3_1
    | spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f367,f215,f377,f126])).

fof(f126,plain,
    ( spl3_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f367,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ v3_tex_2(sK1,sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f221,f217])).

fof(f221,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(forward_demodulation,[],[f34,f143])).

fof(f34,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f361,plain,
    ( spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f183,f325])).

fof(f325,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f193,f217])).

fof(f193,plain,(
    v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(global_subsumption,[],[f39,f188,f192])).

fof(f192,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f191,f143])).

fof(f191,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f189,f143])).

fof(f189,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(superposition,[],[f48,f75])).

fof(f75,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f39,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f188,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f89,f143])).

fof(f183,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl3_3
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f319,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f146,f312])).

fof(f312,plain,
    ( spl3_9
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f146,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f101,f143])).

fof(f101,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f35,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f315,plain,
    ( ~ spl3_9
    | spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f310,f302,f215,f312])).

fof(f302,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f310,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f309,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f309,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | sK1 = k2_subset_1(k2_struct_0(sK0))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f306,f41])).

fof(f306,plain,
    ( ~ r1_tarski(sK1,k2_subset_1(k2_struct_0(sK0)))
    | sK1 = k2_subset_1(k2_struct_0(sK0))
    | ~ spl3_8 ),
    inference(resolution,[],[f303,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f303,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | sK1 = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f302])).

fof(f304,plain,
    ( ~ spl3_1
    | spl3_8 ),
    inference(avatar_split_clause,[],[f296,f302,f126])).

fof(f296,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK1 = X0
      | ~ r1_tarski(sK1,X0)
      | ~ v3_tex_2(sK1,sK0) ) ),
    inference(forward_demodulation,[],[f108,f143])).

fof(f108,plain,(
    ! [X0] :
      ( sK1 = X0
      | ~ r1_tarski(sK1,X0)
      | ~ v3_tex_2(sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f39,f87,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ r1_tarski(sK1,X0)
      | sK1 = X0
      | ~ v3_tex_2(sK1,sK0) ) ),
    inference(resolution,[],[f35,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f87,plain,(
    ! [X8] :
      ( v2_tex_2(X8,sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f86])).

fof(f86,plain,(
    ! [X7] :
      ( v2_tex_2(X7,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f70])).

fof(f70,plain,(
    ! [X1] :
      ( v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f66])).

fof(f66,plain,(
    ! [X1] :
      ( v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f39,f38,f37,f64])).

fof(f64,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X1,sK0) ) ),
    inference(resolution,[],[f36,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f220,plain,
    ( spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f145,f213])).

fof(f213,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl3_4
  <=> v1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f145,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_2 ),
    inference(backward_demodulation,[],[f132,f143])).

fof(f132,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f218,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f178,f215,f211])).

fof(f178,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f147,f58])).

fof(f147,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f35,f143])).

fof(f184,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f112,f181,f126])).

fof(f112,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f36,f37,f39,f111,f100])).

fof(f100,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f35,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f111,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(global_subsumption,[],[f36,f37,f38,f39,f99])).

fof(f99,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f35,f56])).

fof(f133,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f33,f130,f126])).

fof(f33,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.47  % (30078)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.48  % (30087)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.48  % (30078)Refutation not found, incomplete strategy% (30078)------------------------------
% 0.22/0.48  % (30078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (30078)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (30078)Memory used [KB]: 10618
% 0.22/0.48  % (30078)Time elapsed: 0.057 s
% 0.22/0.48  % (30078)------------------------------
% 0.22/0.48  % (30078)------------------------------
% 0.22/0.49  % (30087)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f384,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f133,f184,f218,f220,f304,f315,f319,f361,f380,f383])).
% 0.22/0.49  fof(f383,plain,(
% 0.22/0.49    ~spl3_5 | ~spl3_10),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f381])).
% 0.22/0.49  fof(f381,plain,(
% 0.22/0.49    $false | (~spl3_5 | ~spl3_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f322,f379])).
% 0.22/0.49  fof(f379,plain,(
% 0.22/0.49    v1_subset_1(sK1,sK1) | ~spl3_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f377])).
% 0.22/0.49  fof(f377,plain,(
% 0.22/0.49    spl3_10 <=> v1_subset_1(sK1,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.49  fof(f322,plain,(
% 0.22/0.49    ~v1_subset_1(sK1,sK1) | ~spl3_5),
% 0.22/0.49    inference(backward_demodulation,[],[f144,f217])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    sK1 = k2_struct_0(sK0) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f215])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    spl3_5 <=> sK1 = k2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ~v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.49    inference(backward_demodulation,[],[f90,f143])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.49    inference(global_subsumption,[],[f89,f142])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f90,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(resolution,[],[f74,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    l1_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f39,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f15])).
% 0.22/0.49  fof(f15,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ~v1_subset_1(k2_struct_0(sK0),u1_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f74,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_struct_0(X0) | ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).
% 0.22/0.49  fof(f380,plain,(
% 0.22/0.49    ~spl3_1 | spl3_10 | ~spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f367,f215,f377,f126])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl3_1 <=> v3_tex_2(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f367,plain,(
% 0.22/0.49    v1_subset_1(sK1,sK1) | ~v3_tex_2(sK1,sK0) | ~spl3_5),
% 0.22/0.49    inference(forward_demodulation,[],[f221,f217])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    v1_subset_1(sK1,k2_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.22/0.49    inference(forward_demodulation,[],[f34,f143])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f361,plain,(
% 0.22/0.49    spl3_3 | ~spl3_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f359])).
% 0.22/0.49  fof(f359,plain,(
% 0.22/0.49    $false | (spl3_3 | ~spl3_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f183,f325])).
% 0.22/0.49  fof(f325,plain,(
% 0.22/0.49    v1_tops_1(sK1,sK0) | ~spl3_5),
% 0.22/0.49    inference(backward_demodulation,[],[f193,f217])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.22/0.49    inference(global_subsumption,[],[f39,f188,f192])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.22/0.49    inference(forward_demodulation,[],[f191,f143])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f190])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.22/0.49    inference(forward_demodulation,[],[f189,f143])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.22/0.49    inference(superposition,[],[f48,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f39,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.49    inference(forward_demodulation,[],[f89,f143])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    ~v1_tops_1(sK1,sK0) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f181])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    spl3_3 <=> v1_tops_1(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f319,plain,(
% 0.22/0.49    spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f146,f312])).
% 0.22/0.49  fof(f312,plain,(
% 0.22/0.49    spl3_9 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    r1_tarski(sK1,k2_struct_0(sK0))),
% 0.22/0.49    inference(backward_demodulation,[],[f101,f143])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f35,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f315,plain,(
% 0.22/0.49    ~spl3_9 | spl3_5 | ~spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f310,f302,f215,f312])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    spl3_8 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK1,X0) | sK1 = X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f310,plain,(
% 0.22/0.49    sK1 = k2_struct_0(sK0) | ~r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_8),
% 0.22/0.49    inference(forward_demodulation,[],[f309,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.49  fof(f309,plain,(
% 0.22/0.49    ~r1_tarski(sK1,k2_struct_0(sK0)) | sK1 = k2_subset_1(k2_struct_0(sK0)) | ~spl3_8),
% 0.22/0.49    inference(forward_demodulation,[],[f306,f41])).
% 0.22/0.49  fof(f306,plain,(
% 0.22/0.49    ~r1_tarski(sK1,k2_subset_1(k2_struct_0(sK0))) | sK1 = k2_subset_1(k2_struct_0(sK0)) | ~spl3_8),
% 0.22/0.49    inference(resolution,[],[f303,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.49  fof(f303,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK1,X0) | sK1 = X0) ) | ~spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f302])).
% 0.22/0.49  fof(f304,plain,(
% 0.22/0.49    ~spl3_1 | spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f296,f302,f126])).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = X0 | ~r1_tarski(sK1,X0) | ~v3_tex_2(sK1,sK0)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f108,f143])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ( ! [X0] : (sK1 = X0 | ~r1_tarski(sK1,X0) | ~v3_tex_2(sK1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(global_subsumption,[],[f39,f87,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~r1_tarski(sK1,X0) | sK1 = X0 | ~v3_tex_2(sK1,sK0)) )),
% 0.22/0.49    inference(resolution,[],[f35,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X8] : (v2_tex_2(X8,sK0) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(global_subsumption,[],[f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X7] : (v2_tex_2(X7,sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(global_subsumption,[],[f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0] : (v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(global_subsumption,[],[f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X1] : (v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(global_subsumption,[],[f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X1] : (v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.49    inference(global_subsumption,[],[f39,f38,f37,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X1] : (~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) )),
% 0.22/0.49    inference(resolution,[],[f36,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    v1_tdlat_3(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    spl3_2 | ~spl3_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f219])).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    $false | (spl3_2 | ~spl3_4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f145,f213])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    v1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f211])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    spl3_4 <=> v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ~v1_subset_1(sK1,k2_struct_0(sK0)) | spl3_2),
% 0.22/0.49    inference(backward_demodulation,[],[f132,f143])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl3_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    spl3_4 | spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f178,f215,f211])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    sK1 = k2_struct_0(sK0) | v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f147,f58])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.49    inference(backward_demodulation,[],[f35,f143])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    spl3_1 | ~spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f112,f181,f126])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ~v1_tops_1(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.22/0.49    inference(global_subsumption,[],[f36,f37,f39,f111,f100])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.22/0.49    inference(resolution,[],[f35,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(global_subsumption,[],[f36,f37,f38,f39,f99])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(resolution,[],[f35,f56])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    spl3_1 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f130,f126])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (30087)------------------------------
% 0.22/0.49  % (30087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (30087)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (30087)Memory used [KB]: 10874
% 0.22/0.49  % (30087)Time elapsed: 0.075 s
% 0.22/0.49  % (30087)------------------------------
% 0.22/0.49  % (30087)------------------------------
% 0.22/0.49  % (30065)Success in time 0.132 s
%------------------------------------------------------------------------------
