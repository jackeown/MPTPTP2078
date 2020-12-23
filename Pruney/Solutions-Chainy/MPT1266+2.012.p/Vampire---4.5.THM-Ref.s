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
% DateTime   : Thu Dec  3 13:12:24 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 852 expanded)
%              Number of leaves         :   24 ( 247 expanded)
%              Depth                    :   19
%              Number of atoms          :  409 (3327 expanded)
%              Number of equality atoms :   78 ( 964 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f498,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f84,f168,f185,f255,f300,f325,f349,f355,f382,f497])).

fof(f497,plain,
    ( ~ spl3_5
    | ~ spl3_11
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f496])).

fof(f496,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11
    | spl3_12 ),
    inference(subsumption_resolution,[],[f495,f131])).

fof(f131,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_5
  <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f495,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_11
    | spl3_12 ),
    inference(forward_demodulation,[],[f494,f86])).

fof(f86,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f85,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f85,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f44,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f494,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11
    | spl3_12 ),
    inference(subsumption_resolution,[],[f493,f44])).

fof(f493,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_11
    | spl3_12 ),
    inference(subsumption_resolution,[],[f492,f184])).

fof(f184,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl3_12
  <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f492,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_11 ),
    inference(trivial_inequality_removal,[],[f491])).

fof(f491,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_11 ),
    inference(superposition,[],[f55,f180])).

fof(f180,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f382,plain,
    ( spl3_1
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | spl3_1
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f380,f87])).

fof(f87,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f45,f86])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f380,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_1
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f379,f78])).

fof(f78,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f379,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(resolution,[],[f183,f99])).

fof(f99,plain,(
    ! [X2] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0)
      | v2_tops_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f94,plain,(
    ! [X2] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0)
      | v2_tops_1(X2,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f57,f86])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f183,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f355,plain,
    ( ~ spl3_5
    | ~ spl3_11
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_11
    | spl3_13 ),
    inference(subsumption_resolution,[],[f353,f312])).

fof(f312,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f171,f180])).

fof(f171,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ spl3_5 ),
    inference(resolution,[],[f131,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f97,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

% (8707)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f92,f44])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f62,f86])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f353,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_11
    | spl3_13 ),
    inference(resolution,[],[f350,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f350,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_11
    | spl3_13 ),
    inference(forward_demodulation,[],[f192,f180])).

fof(f192,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl3_13
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f349,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f347,f82])).

fof(f82,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f347,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f320,f346])).

fof(f346,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f343,f310])).

fof(f310,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f236,f180])).

fof(f236,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(resolution,[],[f171,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f69,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f343,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)))
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(resolution,[],[f305,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f305,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f191,f180])).

fof(f191,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f190])).

fof(f320,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f163,f180])).

fof(f163,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f101,f87])).

fof(f101,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X4) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X4))) ) ),
    inference(subsumption_resolution,[],[f96,f44])).

fof(f96,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X4) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X4)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f53,f86])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f325,plain,
    ( ~ spl3_1
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl3_1
    | spl3_12 ),
    inference(subsumption_resolution,[],[f77,f304])).

fof(f304,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl3_12 ),
    inference(subsumption_resolution,[],[f204,f184])).

fof(f204,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f118,f88])).

fof(f88,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f87,f66])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f98,f67])).

fof(f98,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_tops_1(X1,sK0)
      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X1),sK0) ) ),
    inference(subsumption_resolution,[],[f93,f44])).

fof(f93,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_tops_1(X1,sK0)
      | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X1),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f56,f86])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f300,plain,
    ( ~ spl3_2
    | ~ spl3_5
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_5
    | spl3_13 ),
    inference(subsumption_resolution,[],[f298,f257])).

fof(f257,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f171,f253])).

fof(f253,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f252,f71])).

fof(f71,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f252,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f248,f164])).

fof(f164,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f163,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f248,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))
    | ~ spl3_5 ),
    inference(resolution,[],[f116,f131])).

fof(f116,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X1) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X1))) ) ),
    inference(resolution,[],[f97,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f298,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl3_2
    | ~ spl3_5
    | spl3_13 ),
    inference(resolution,[],[f279,f67])).

fof(f279,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_5
    | spl3_13 ),
    inference(forward_demodulation,[],[f192,f253])).

fof(f255,plain,
    ( ~ spl3_2
    | ~ spl3_5
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_5
    | spl3_11 ),
    inference(subsumption_resolution,[],[f253,f179])).

fof(f179,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f185,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f170,f130,f182,f178])).

fof(f170,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl3_5 ),
    inference(resolution,[],[f131,f100])).

fof(f100,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X3,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X3) ) ),
    inference(subsumption_resolution,[],[f95,f44])).

fof(f95,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X3,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X3)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f54,f86])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f168,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f165,f87])).

fof(f165,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_5 ),
    inference(resolution,[],[f132,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f132,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f84,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f46,f80,f76])).

fof(f46,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f47,f80,f76])).

fof(f47,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (8705)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (8697)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (8682)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (8684)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (8690)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (8695)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (8694)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (8689)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (8704)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (8686)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (8696)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (8709)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (8687)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (8704)Refutation not found, incomplete strategy% (8704)------------------------------
% 0.21/0.54  % (8704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8704)Memory used [KB]: 10746
% 0.21/0.54  % (8704)Time elapsed: 0.090 s
% 0.21/0.54  % (8704)------------------------------
% 0.21/0.54  % (8704)------------------------------
% 0.21/0.54  % (8685)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (8688)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (8703)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.54  % (8690)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % SZS output start Proof for theBenchmark
% 1.38/0.54  fof(f498,plain,(
% 1.38/0.54    $false),
% 1.38/0.54    inference(avatar_sat_refutation,[],[f83,f84,f168,f185,f255,f300,f325,f349,f355,f382,f497])).
% 1.38/0.54  fof(f497,plain,(
% 1.38/0.54    ~spl3_5 | ~spl3_11 | spl3_12),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f496])).
% 1.38/0.54  fof(f496,plain,(
% 1.38/0.54    $false | (~spl3_5 | ~spl3_11 | spl3_12)),
% 1.38/0.54    inference(subsumption_resolution,[],[f495,f131])).
% 1.38/0.54  fof(f131,plain,(
% 1.38/0.54    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_5),
% 1.38/0.54    inference(avatar_component_clause,[],[f130])).
% 1.38/0.54  fof(f130,plain,(
% 1.38/0.54    spl3_5 <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.38/0.54  fof(f495,plain,(
% 1.38/0.54    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_11 | spl3_12)),
% 1.38/0.54    inference(forward_demodulation,[],[f494,f86])).
% 1.38/0.54  fof(f86,plain,(
% 1.38/0.54    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.38/0.54    inference(resolution,[],[f85,f51])).
% 1.38/0.54  fof(f51,plain,(
% 1.38/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f20])).
% 1.38/0.54  fof(f20,plain,(
% 1.38/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f11])).
% 1.38/0.54  fof(f11,axiom,(
% 1.38/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.38/0.54  fof(f85,plain,(
% 1.38/0.54    l1_struct_0(sK0)),
% 1.38/0.54    inference(resolution,[],[f44,f52])).
% 1.38/0.54  fof(f52,plain,(
% 1.38/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f21])).
% 1.38/0.54  fof(f21,plain,(
% 1.38/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f13])).
% 1.38/0.54  fof(f13,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.38/0.54  fof(f44,plain,(
% 1.38/0.54    l1_pre_topc(sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f35])).
% 1.38/0.54  fof(f35,plain,(
% 1.38/0.54    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f34,plain,(
% 1.38/0.54    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f32,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f31])).
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f19])).
% 1.38/0.54  fof(f19,plain,(
% 1.38/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f18])).
% 1.38/0.54  fof(f18,negated_conjecture,(
% 1.38/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.38/0.54    inference(negated_conjecture,[],[f17])).
% 1.38/0.54  fof(f17,conjecture,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.38/0.54  fof(f494,plain,(
% 1.38/0.54    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_11 | spl3_12)),
% 1.38/0.54    inference(subsumption_resolution,[],[f493,f44])).
% 1.38/0.54  fof(f493,plain,(
% 1.38/0.54    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_11 | spl3_12)),
% 1.38/0.54    inference(subsumption_resolution,[],[f492,f184])).
% 1.38/0.54  fof(f184,plain,(
% 1.38/0.54    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | spl3_12),
% 1.38/0.54    inference(avatar_component_clause,[],[f182])).
% 1.38/0.54  fof(f182,plain,(
% 1.38/0.54    spl3_12 <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.38/0.54  fof(f492,plain,(
% 1.38/0.54    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_11),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f491])).
% 1.38/0.54  fof(f491,plain,(
% 1.38/0.54    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_11),
% 1.38/0.54    inference(superposition,[],[f55,f180])).
% 1.38/0.54  fof(f180,plain,(
% 1.38/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl3_11),
% 1.38/0.54    inference(avatar_component_clause,[],[f178])).
% 1.38/0.54  fof(f178,plain,(
% 1.38/0.54    spl3_11 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.38/0.54  fof(f55,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f36])).
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f23])).
% 1.38/0.54  fof(f23,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f15])).
% 1.38/0.54  fof(f15,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 1.38/0.54  fof(f382,plain,(
% 1.38/0.54    spl3_1 | ~spl3_12),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f381])).
% 1.38/0.54  fof(f381,plain,(
% 1.38/0.54    $false | (spl3_1 | ~spl3_12)),
% 1.38/0.54    inference(subsumption_resolution,[],[f380,f87])).
% 1.38/0.54  fof(f87,plain,(
% 1.38/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.38/0.54    inference(backward_demodulation,[],[f45,f86])).
% 1.38/0.54  fof(f45,plain,(
% 1.38/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.54    inference(cnf_transformation,[],[f35])).
% 1.38/0.54  fof(f380,plain,(
% 1.38/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (spl3_1 | ~spl3_12)),
% 1.38/0.54    inference(subsumption_resolution,[],[f379,f78])).
% 1.38/0.54  fof(f78,plain,(
% 1.38/0.54    ~v2_tops_1(sK1,sK0) | spl3_1),
% 1.38/0.54    inference(avatar_component_clause,[],[f76])).
% 1.38/0.54  fof(f76,plain,(
% 1.38/0.54    spl3_1 <=> v2_tops_1(sK1,sK0)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.38/0.54  fof(f379,plain,(
% 1.38/0.54    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_12),
% 1.38/0.54    inference(resolution,[],[f183,f99])).
% 1.38/0.54  fof(f99,plain,(
% 1.38/0.54    ( ! [X2] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0) | v2_tops_1(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f94,f44])).
% 1.38/0.54  fof(f94,plain,(
% 1.38/0.54    ( ! [X2] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X2),sK0) | v2_tops_1(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.38/0.54    inference(superposition,[],[f57,f86])).
% 1.38/0.54  fof(f57,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f37])).
% 1.38/0.54  fof(f37,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f16])).
% 1.38/0.54  fof(f16,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 1.38/0.54  fof(f183,plain,(
% 1.38/0.54    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~spl3_12),
% 1.38/0.54    inference(avatar_component_clause,[],[f182])).
% 1.38/0.54  fof(f355,plain,(
% 1.38/0.54    ~spl3_5 | ~spl3_11 | spl3_13),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f354])).
% 1.38/0.54  fof(f354,plain,(
% 1.38/0.54    $false | (~spl3_5 | ~spl3_11 | spl3_13)),
% 1.38/0.54    inference(subsumption_resolution,[],[f353,f312])).
% 1.38/0.54  fof(f312,plain,(
% 1.38/0.54    r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_5 | ~spl3_11)),
% 1.38/0.54    inference(forward_demodulation,[],[f171,f180])).
% 1.38/0.54  fof(f171,plain,(
% 1.38/0.54    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) | ~spl3_5),
% 1.38/0.54    inference(resolution,[],[f131,f115])).
% 1.38/0.54  fof(f115,plain,(
% 1.38/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_pre_topc(sK0,X0),k2_struct_0(sK0))) )),
% 1.38/0.54    inference(resolution,[],[f97,f66])).
% 1.38/0.54  fof(f66,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f42])).
% 1.38/0.54  fof(f42,plain,(
% 1.38/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.38/0.54    inference(nnf_transformation,[],[f10])).
% 1.38/0.54  % (8707)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  fof(f10,axiom,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.38/0.54  fof(f97,plain,(
% 1.38/0.54    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f92,f44])).
% 1.38/0.54  fof(f92,plain,(
% 1.38/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.38/0.54    inference(superposition,[],[f62,f86])).
% 1.38/0.54  fof(f62,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(flattening,[],[f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f12])).
% 1.38/0.54  fof(f12,axiom,(
% 1.38/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.38/0.54  fof(f353,plain,(
% 1.38/0.54    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_11 | spl3_13)),
% 1.38/0.54    inference(resolution,[],[f350,f67])).
% 1.38/0.54  fof(f67,plain,(
% 1.38/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f42])).
% 1.38/0.54  fof(f350,plain,(
% 1.38/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_11 | spl3_13)),
% 1.38/0.54    inference(forward_demodulation,[],[f192,f180])).
% 1.38/0.54  fof(f192,plain,(
% 1.38/0.54    ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_13),
% 1.38/0.54    inference(avatar_component_clause,[],[f190])).
% 1.38/0.54  fof(f190,plain,(
% 1.38/0.54    spl3_13 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.38/0.54  fof(f349,plain,(
% 1.38/0.54    spl3_2 | ~spl3_5 | ~spl3_11 | ~spl3_13),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f348])).
% 1.38/0.54  fof(f348,plain,(
% 1.38/0.54    $false | (spl3_2 | ~spl3_5 | ~spl3_11 | ~spl3_13)),
% 1.38/0.54    inference(subsumption_resolution,[],[f347,f82])).
% 1.38/0.54  fof(f82,plain,(
% 1.38/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl3_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f80])).
% 1.38/0.54  fof(f80,plain,(
% 1.38/0.54    spl3_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.38/0.54  fof(f347,plain,(
% 1.38/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl3_5 | ~spl3_11 | ~spl3_13)),
% 1.38/0.54    inference(backward_demodulation,[],[f320,f346])).
% 1.38/0.54  fof(f346,plain,(
% 1.38/0.54    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_5 | ~spl3_11 | ~spl3_13)),
% 1.38/0.54    inference(forward_demodulation,[],[f343,f310])).
% 1.38/0.54  fof(f310,plain,(
% 1.38/0.54    k1_xboole_0 = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))) | (~spl3_5 | ~spl3_11)),
% 1.38/0.54    inference(forward_demodulation,[],[f236,f180])).
% 1.38/0.54  fof(f236,plain,(
% 1.38/0.54    k1_xboole_0 = k5_xboole_0(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))) | ~spl3_5),
% 1.38/0.54    inference(resolution,[],[f171,f73])).
% 1.38/0.54  fof(f73,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f69,f58])).
% 1.38/0.54  fof(f58,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.54  fof(f69,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f43])).
% 1.38/0.54  fof(f43,plain,(
% 1.38/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.38/0.54    inference(nnf_transformation,[],[f2])).
% 1.38/0.54  fof(f2,axiom,(
% 1.38/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.38/0.54  fof(f343,plain,(
% 1.38/0.54    k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k3_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))) | (~spl3_11 | ~spl3_13)),
% 1.38/0.54    inference(resolution,[],[f305,f72])).
% 1.38/0.54  fof(f72,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f60,f58])).
% 1.38/0.54  fof(f60,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f26])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f6])).
% 1.38/0.54  fof(f6,axiom,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.38/0.54  fof(f305,plain,(
% 1.38/0.54    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_11 | ~spl3_13)),
% 1.38/0.54    inference(backward_demodulation,[],[f191,f180])).
% 1.38/0.54  fof(f191,plain,(
% 1.38/0.54    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_13),
% 1.38/0.54    inference(avatar_component_clause,[],[f190])).
% 1.38/0.54  fof(f320,plain,(
% 1.38/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl3_11),
% 1.38/0.54    inference(forward_demodulation,[],[f163,f180])).
% 1.38/0.54  fof(f163,plain,(
% 1.38/0.54    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 1.38/0.54    inference(resolution,[],[f101,f87])).
% 1.38/0.54  fof(f101,plain,(
% 1.38/0.54    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X4) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X4)))) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f96,f44])).
% 1.38/0.54  fof(f96,plain,(
% 1.38/0.54    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X4) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X4))) | ~l1_pre_topc(sK0)) )),
% 1.38/0.54    inference(superposition,[],[f53,f86])).
% 1.38/0.54  fof(f53,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f22])).
% 1.38/0.54  fof(f22,plain,(
% 1.38/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.54    inference(ennf_transformation,[],[f14])).
% 1.38/0.54  fof(f14,axiom,(
% 1.38/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 1.38/0.54  fof(f325,plain,(
% 1.38/0.54    ~spl3_1 | spl3_12),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f324])).
% 1.38/0.54  fof(f324,plain,(
% 1.38/0.54    $false | (~spl3_1 | spl3_12)),
% 1.38/0.54    inference(subsumption_resolution,[],[f77,f304])).
% 1.38/0.54  fof(f304,plain,(
% 1.38/0.54    ~v2_tops_1(sK1,sK0) | spl3_12),
% 1.38/0.54    inference(subsumption_resolution,[],[f204,f184])).
% 1.38/0.54  fof(f204,plain,(
% 1.38/0.54    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(resolution,[],[f118,f88])).
% 1.38/0.54  fof(f88,plain,(
% 1.38/0.54    r1_tarski(sK1,k2_struct_0(sK0))),
% 1.38/0.54    inference(resolution,[],[f87,f66])).
% 1.38/0.54  fof(f118,plain,(
% 1.38/0.54    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v2_tops_1(X0,sK0)) )),
% 1.38/0.54    inference(resolution,[],[f98,f67])).
% 1.38/0.54  fof(f98,plain,(
% 1.38/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X1,sK0) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X1),sK0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f93,f44])).
% 1.38/0.54  fof(f93,plain,(
% 1.38/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X1,sK0) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),X1),sK0) | ~l1_pre_topc(sK0)) )),
% 1.38/0.54    inference(superposition,[],[f56,f86])).
% 1.38/0.54  fof(f56,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f37])).
% 1.38/0.54  fof(f77,plain,(
% 1.38/0.54    v2_tops_1(sK1,sK0) | ~spl3_1),
% 1.38/0.54    inference(avatar_component_clause,[],[f76])).
% 1.38/0.54  fof(f300,plain,(
% 1.38/0.54    ~spl3_2 | ~spl3_5 | spl3_13),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f299])).
% 1.38/0.54  fof(f299,plain,(
% 1.38/0.54    $false | (~spl3_2 | ~spl3_5 | spl3_13)),
% 1.38/0.54    inference(subsumption_resolution,[],[f298,f257])).
% 1.38/0.54  fof(f257,plain,(
% 1.38/0.54    r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_2 | ~spl3_5)),
% 1.38/0.54    inference(backward_demodulation,[],[f171,f253])).
% 1.38/0.54  fof(f253,plain,(
% 1.38/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl3_2 | ~spl3_5)),
% 1.38/0.54    inference(forward_demodulation,[],[f252,f71])).
% 1.38/0.54  fof(f71,plain,(
% 1.38/0.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.38/0.54    inference(definition_unfolding,[],[f49,f70])).
% 1.38/0.54  fof(f70,plain,(
% 1.38/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f50,f48])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.38/0.54  fof(f50,plain,(
% 1.38/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f9])).
% 1.38/0.54  fof(f9,axiom,(
% 1.38/0.54    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.38/0.54  fof(f49,plain,(
% 1.38/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f5])).
% 1.38/0.54  fof(f5,axiom,(
% 1.38/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.38/0.54  fof(f252,plain,(
% 1.38/0.54    k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl3_2 | ~spl3_5)),
% 1.38/0.54    inference(forward_demodulation,[],[f248,f164])).
% 1.38/0.54  fof(f164,plain,(
% 1.38/0.54    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl3_2),
% 1.38/0.54    inference(forward_demodulation,[],[f163,f81])).
% 1.38/0.54  fof(f81,plain,(
% 1.38/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f80])).
% 1.38/0.54  fof(f248,plain,(
% 1.38/0.54    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) | ~spl3_5),
% 1.38/0.54    inference(resolution,[],[f116,f131])).
% 1.38/0.54  fof(f116,plain,(
% 1.38/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X1) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X1)))) )),
% 1.38/0.54    inference(resolution,[],[f97,f61])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.38/0.54    inference(cnf_transformation,[],[f27])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f8])).
% 1.38/0.54  fof(f8,axiom,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.38/0.54  fof(f298,plain,(
% 1.38/0.54    ~r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl3_2 | ~spl3_5 | spl3_13)),
% 1.38/0.54    inference(resolution,[],[f279,f67])).
% 1.38/0.54  fof(f279,plain,(
% 1.38/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_2 | ~spl3_5 | spl3_13)),
% 1.38/0.54    inference(forward_demodulation,[],[f192,f253])).
% 1.38/0.54  fof(f255,plain,(
% 1.38/0.54    ~spl3_2 | ~spl3_5 | spl3_11),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f254])).
% 1.38/0.54  fof(f254,plain,(
% 1.38/0.54    $false | (~spl3_2 | ~spl3_5 | spl3_11)),
% 1.38/0.54    inference(subsumption_resolution,[],[f253,f179])).
% 1.38/0.54  fof(f179,plain,(
% 1.38/0.54    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | spl3_11),
% 1.38/0.54    inference(avatar_component_clause,[],[f178])).
% 1.38/0.54  fof(f185,plain,(
% 1.38/0.54    spl3_11 | ~spl3_12 | ~spl3_5),
% 1.38/0.54    inference(avatar_split_clause,[],[f170,f130,f182,f178])).
% 1.38/0.54  fof(f170,plain,(
% 1.38/0.54    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl3_5),
% 1.38/0.54    inference(resolution,[],[f131,f100])).
% 1.38/0.54  fof(f100,plain,(
% 1.38/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X3,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X3)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f95,f44])).
% 1.38/0.54  fof(f95,plain,(
% 1.38/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X3,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X3) | ~l1_pre_topc(sK0)) )),
% 1.38/0.54    inference(superposition,[],[f54,f86])).
% 1.38/0.54  fof(f54,plain,(
% 1.38/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f36])).
% 1.38/0.54  fof(f168,plain,(
% 1.38/0.54    spl3_5),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f167])).
% 1.38/0.54  fof(f167,plain,(
% 1.38/0.54    $false | spl3_5),
% 1.38/0.54    inference(subsumption_resolution,[],[f165,f87])).
% 1.38/0.54  fof(f165,plain,(
% 1.38/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl3_5),
% 1.38/0.54    inference(resolution,[],[f132,f59])).
% 1.38/0.54  fof(f59,plain,(
% 1.38/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f25])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.38/0.54    inference(ennf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.38/0.54  fof(f132,plain,(
% 1.38/0.54    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_5),
% 1.38/0.54    inference(avatar_component_clause,[],[f130])).
% 1.38/0.54  fof(f84,plain,(
% 1.38/0.54    spl3_1 | spl3_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f46,f80,f76])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f35])).
% 1.38/0.54  fof(f83,plain,(
% 1.38/0.54    ~spl3_1 | ~spl3_2),
% 1.38/0.54    inference(avatar_split_clause,[],[f47,f80,f76])).
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 1.38/0.54    inference(cnf_transformation,[],[f35])).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (8690)------------------------------
% 1.38/0.54  % (8690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (8690)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (8690)Memory used [KB]: 10874
% 1.38/0.54  % (8690)Time elapsed: 0.123 s
% 1.38/0.54  % (8690)------------------------------
% 1.38/0.54  % (8690)------------------------------
% 1.38/0.55  % (8701)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.55  % (8708)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (8681)Success in time 0.188 s
%------------------------------------------------------------------------------
