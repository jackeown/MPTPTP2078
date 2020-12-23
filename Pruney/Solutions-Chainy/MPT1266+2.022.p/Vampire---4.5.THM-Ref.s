%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 492 expanded)
%              Number of leaves         :   25 ( 162 expanded)
%              Depth                    :   16
%              Number of atoms          :  359 (1466 expanded)
%              Number of equality atoms :   81 ( 481 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f147,f192,f409,f415,f417,f431,f433,f513,f530,f535,f536])).

fof(f536,plain,
    ( spl2_1
    | ~ spl2_29
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f418,f406,f412,f59])).

fof(f59,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f412,plain,
    ( spl2_29
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f406,plain,
    ( spl2_28
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f418,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(sK1,sK0)
    | ~ spl2_28 ),
    inference(resolution,[],[f408,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).

fof(f31,plain,
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

% (13713)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f32,plain,
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

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f408,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f406])).

fof(f535,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f68,f61])).

fof(f61,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f68,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f39,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f39,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f530,plain,
    ( spl2_2
    | ~ spl2_31
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | spl2_2
    | ~ spl2_31
    | ~ spl2_34 ),
    inference(trivial_inequality_removal,[],[f528])).

fof(f528,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_2
    | ~ spl2_31
    | ~ spl2_34 ),
    inference(superposition,[],[f64,f524])).

fof(f524,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_31
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f516,f76])).

fof(f76,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f73,f56])).

fof(f56,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f41,f55])).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f40,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f52,f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f516,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl2_31
    | ~ spl2_34 ),
    inference(backward_demodulation,[],[f439,f512])).

fof(f512,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl2_34
  <=> u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f439,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_31 ),
    inference(resolution,[],[f430,f52])).

fof(f430,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl2_31
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f64,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f513,plain,
    ( ~ spl2_12
    | ~ spl2_10
    | spl2_34
    | ~ spl2_28
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f508,f424,f406,f510,f137,f184])).

fof(f184,plain,
    ( spl2_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f137,plain,
    ( spl2_10
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f424,plain,
    ( spl2_30
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f508,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_28
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f420,f450])).

fof(f450,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f445,f199])).

fof(f199,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f193,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f193,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f46,f36])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f445,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_30 ),
    inference(resolution,[],[f425,f52])).

fof(f425,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f424])).

fof(f420,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_28 ),
    inference(forward_demodulation,[],[f419,f174])).

fof(f174,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f173,f87])).

fof(f87,plain,(
    ! [X0] : k4_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f82,f76])).

fof(f82,plain,(
    ! [X0] : k4_subset_1(X0,X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f81,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f69,f42])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f51,f56])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f57,f56])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k3_subset_1(X0,k1_xboole_0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f55])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f173,plain,(
    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f167,f76])).

fof(f167,plain,(
    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(resolution,[],[f166,f70])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ) ),
    inference(resolution,[],[f165,f36])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

fof(f419,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_28 ),
    inference(resolution,[],[f408,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f433,plain,
    ( ~ spl2_12
    | ~ spl2_10
    | spl2_30 ),
    inference(avatar_split_clause,[],[f432,f424,f137,f184])).

fof(f432,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_30 ),
    inference(resolution,[],[f426,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f426,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_30 ),
    inference(avatar_component_clause,[],[f424])).

fof(f431,plain,
    ( ~ spl2_30
    | spl2_31 ),
    inference(avatar_split_clause,[],[f422,f428,f424])).

fof(f422,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f51,f199])).

fof(f417,plain,(
    spl2_29 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl2_29 ),
    inference(resolution,[],[f414,f37])).

fof(f414,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f412])).

fof(f415,plain,
    ( ~ spl2_12
    | ~ spl2_29
    | spl2_28
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f410,f59,f406,f412,f184])).

fof(f410,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f409,plain,
    ( ~ spl2_12
    | ~ spl2_10
    | spl2_28
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f398,f137,f63,f406,f137,f184])).

fof(f398,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f397])).

fof(f397,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f395,f174])).

fof(f395,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(superposition,[],[f48,f389])).

fof(f389,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f388,f56])).

fof(f388,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f374,f203])).

fof(f203,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f199,f65])).

fof(f374,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_10 ),
    inference(resolution,[],[f350,f138])).

fof(f138,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f350,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0))) ) ),
    inference(resolution,[],[f80,f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0))) ) ),
    inference(resolution,[],[f54,f52])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f192,plain,(
    spl2_12 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl2_12 ),
    inference(resolution,[],[f186,f36])).

fof(f186,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f184])).

fof(f147,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl2_10 ),
    inference(resolution,[],[f145,f37])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_10 ),
    inference(resolution,[],[f139,f51])).

fof(f139,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f66,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f38,f63,f59])).

fof(f38,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:25:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (13711)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.45  % (13711)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f537,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f66,f147,f192,f409,f415,f417,f431,f433,f513,f530,f535,f536])).
% 0.20/0.45  fof(f536,plain,(
% 0.20/0.45    spl2_1 | ~spl2_29 | ~spl2_28),
% 0.20/0.45    inference(avatar_split_clause,[],[f418,f406,f412,f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.45  fof(f412,plain,(
% 0.20/0.45    spl2_29 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.20/0.45  fof(f406,plain,(
% 0.20/0.45    spl2_28 <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.20/0.45  fof(f418,plain,(
% 0.20/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0) | ~spl2_28),
% 0.20/0.45    inference(resolution,[],[f408,f98])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) )),
% 0.20/0.45    inference(resolution,[],[f50,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f32,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  % (13713)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.46    inference(negated_conjecture,[],[f15])).
% 0.20/0.46  fof(f15,conjecture,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 0.20/0.46  fof(f408,plain,(
% 0.20/0.46    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_28),
% 0.20/0.46    inference(avatar_component_clause,[],[f406])).
% 0.20/0.46  fof(f535,plain,(
% 0.20/0.46    ~spl2_1 | ~spl2_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f534])).
% 0.20/0.46  fof(f534,plain,(
% 0.20/0.46    $false | (~spl2_1 | ~spl2_2)),
% 0.20/0.46    inference(resolution,[],[f68,f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    v2_tops_1(sK1,sK0) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f59])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ~v2_tops_1(sK1,sK0) | ~spl2_2),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    k1_xboole_0 != k1_xboole_0 | ~v2_tops_1(sK1,sK0) | ~spl2_2),
% 0.20/0.46    inference(forward_demodulation,[],[f39,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f33])).
% 0.20/0.46  fof(f530,plain,(
% 0.20/0.46    spl2_2 | ~spl2_31 | ~spl2_34),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f529])).
% 0.20/0.46  fof(f529,plain,(
% 0.20/0.46    $false | (spl2_2 | ~spl2_31 | ~spl2_34)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f528])).
% 0.20/0.46  fof(f528,plain,(
% 0.20/0.46    k1_xboole_0 != k1_xboole_0 | (spl2_2 | ~spl2_31 | ~spl2_34)),
% 0.20/0.46    inference(superposition,[],[f64,f524])).
% 0.20/0.46  fof(f524,plain,(
% 0.20/0.46    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_31 | ~spl2_34)),
% 0.20/0.46    inference(forward_demodulation,[],[f516,f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) )),
% 0.20/0.46    inference(forward_demodulation,[],[f73,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f41,f55])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f43,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))) )),
% 0.20/0.46    inference(resolution,[],[f52,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.46  fof(f516,plain,(
% 0.20/0.46    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl2_31 | ~spl2_34)),
% 0.20/0.46    inference(backward_demodulation,[],[f439,f512])).
% 0.20/0.46  fof(f512,plain,(
% 0.20/0.46    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_34),
% 0.20/0.46    inference(avatar_component_clause,[],[f510])).
% 0.20/0.46  fof(f510,plain,(
% 0.20/0.46    spl2_34 <=> u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.46  fof(f439,plain,(
% 0.20/0.46    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | ~spl2_31),
% 0.20/0.46    inference(resolution,[],[f430,f52])).
% 0.20/0.46  fof(f430,plain,(
% 0.20/0.46    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_31),
% 0.20/0.46    inference(avatar_component_clause,[],[f428])).
% 0.20/0.46  fof(f428,plain,(
% 0.20/0.46    spl2_31 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f63])).
% 0.20/0.46  fof(f513,plain,(
% 0.20/0.46    ~spl2_12 | ~spl2_10 | spl2_34 | ~spl2_28 | ~spl2_30),
% 0.20/0.46    inference(avatar_split_clause,[],[f508,f424,f406,f510,f137,f184])).
% 0.20/0.46  fof(f184,plain,(
% 0.20/0.46    spl2_12 <=> l1_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    spl2_10 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.46  fof(f424,plain,(
% 0.20/0.46    spl2_30 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.20/0.46  fof(f508,plain,(
% 0.20/0.46    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_28 | ~spl2_30)),
% 0.20/0.46    inference(forward_demodulation,[],[f420,f450])).
% 0.20/0.46  fof(f450,plain,(
% 0.20/0.46    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~spl2_30),
% 0.20/0.46    inference(forward_demodulation,[],[f445,f199])).
% 0.20/0.46  fof(f199,plain,(
% 0.20/0.46    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.46    inference(resolution,[],[f193,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f33])).
% 0.20/0.46  fof(f193,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 0.20/0.46    inference(resolution,[],[f46,f36])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.20/0.46  fof(f445,plain,(
% 0.20/0.46    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_30),
% 0.20/0.46    inference(resolution,[],[f425,f52])).
% 0.20/0.46  fof(f425,plain,(
% 0.20/0.46    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_30),
% 0.20/0.46    inference(avatar_component_clause,[],[f424])).
% 0.20/0.46  fof(f420,plain,(
% 0.20/0.46    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_28),
% 0.20/0.46    inference(forward_demodulation,[],[f419,f174])).
% 0.20/0.46  fof(f174,plain,(
% 0.20/0.46    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.46    inference(forward_demodulation,[],[f173,f87])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ( ! [X0] : (k4_subset_1(X0,X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(forward_demodulation,[],[f82,f76])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X0] : (k4_subset_1(X0,X0,k3_subset_1(X0,X0)) = X0) )),
% 0.20/0.46    inference(resolution,[],[f81,f70])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(resolution,[],[f69,f42])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(superposition,[],[f51,f56])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 0.20/0.46    inference(forward_demodulation,[],[f57,f56])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k3_subset_1(X0,k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f53,f55])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 0.20/0.46  fof(f173,plain,(
% 0.20/0.46    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k1_xboole_0)),
% 0.20/0.46    inference(forward_demodulation,[],[f167,f76])).
% 0.20/0.46  fof(f167,plain,(
% 0.20/0.46    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.20/0.46    inference(resolution,[],[f166,f70])).
% 0.20/0.46  fof(f166,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)) )),
% 0.20/0.46    inference(resolution,[],[f165,f36])).
% 0.20/0.46  fof(f165,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_pre_topc(X1) | k4_subset_1(u1_struct_0(X1),X0,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.20/0.46    inference(resolution,[],[f44,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).
% 0.20/0.46  fof(f419,plain,(
% 0.20/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_28),
% 0.20/0.46    inference(resolution,[],[f408,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.46  fof(f433,plain,(
% 0.20/0.46    ~spl2_12 | ~spl2_10 | spl2_30),
% 0.20/0.46    inference(avatar_split_clause,[],[f432,f424,f137,f184])).
% 0.20/0.46  fof(f432,plain,(
% 0.20/0.46    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_30),
% 0.20/0.46    inference(resolution,[],[f426,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.46  fof(f426,plain,(
% 0.20/0.46    ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_30),
% 0.20/0.46    inference(avatar_component_clause,[],[f424])).
% 0.20/0.46  fof(f431,plain,(
% 0.20/0.46    ~spl2_30 | spl2_31),
% 0.20/0.46    inference(avatar_split_clause,[],[f422,f428,f424])).
% 0.20/0.46  fof(f422,plain,(
% 0.20/0.46    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(superposition,[],[f51,f199])).
% 0.20/0.46  fof(f417,plain,(
% 0.20/0.46    spl2_29),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f416])).
% 0.20/0.46  fof(f416,plain,(
% 0.20/0.46    $false | spl2_29),
% 0.20/0.46    inference(resolution,[],[f414,f37])).
% 0.20/0.46  fof(f414,plain,(
% 0.20/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_29),
% 0.20/0.46    inference(avatar_component_clause,[],[f412])).
% 0.20/0.46  fof(f415,plain,(
% 0.20/0.46    ~spl2_12 | ~spl2_29 | spl2_28 | ~spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f410,f59,f406,f412,f184])).
% 0.20/0.46  fof(f410,plain,(
% 0.20/0.46    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.20/0.46    inference(resolution,[],[f61,f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f35])).
% 0.20/0.46  fof(f409,plain,(
% 0.20/0.46    ~spl2_12 | ~spl2_10 | spl2_28 | ~spl2_2 | ~spl2_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f398,f137,f63,f406,f137,f184])).
% 0.20/0.46  fof(f398,plain,(
% 0.20/0.46    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_10)),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f397])).
% 0.20/0.46  fof(f397,plain,(
% 0.20/0.46    u1_struct_0(sK0) != u1_struct_0(sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_10)),
% 0.20/0.46    inference(forward_demodulation,[],[f395,f174])).
% 0.20/0.46  fof(f395,plain,(
% 0.20/0.46    u1_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_10)),
% 0.20/0.46    inference(superposition,[],[f48,f389])).
% 0.20/0.46  fof(f389,plain,(
% 0.20/0.46    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_10)),
% 0.20/0.46    inference(forward_demodulation,[],[f388,f56])).
% 0.20/0.46  fof(f388,plain,(
% 0.20/0.46    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_10)),
% 0.20/0.46    inference(forward_demodulation,[],[f374,f203])).
% 0.20/0.46  fof(f203,plain,(
% 0.20/0.46    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_2),
% 0.20/0.46    inference(forward_demodulation,[],[f199,f65])).
% 0.20/0.46  fof(f374,plain,(
% 0.20/0.46    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | ~spl2_10),
% 0.20/0.46    inference(resolution,[],[f350,f138])).
% 0.20/0.46  fof(f138,plain,(
% 0.20/0.46    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f137])).
% 0.20/0.46  fof(f350,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0)))) )),
% 0.20/0.46    inference(resolution,[],[f80,f36])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0)))) )),
% 0.20/0.46    inference(resolution,[],[f54,f52])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f192,plain,(
% 0.20/0.46    spl2_12),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f191])).
% 0.20/0.46  fof(f191,plain,(
% 0.20/0.46    $false | spl2_12),
% 0.20/0.46    inference(resolution,[],[f186,f36])).
% 0.20/0.46  fof(f186,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | spl2_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f184])).
% 0.20/0.46  fof(f147,plain,(
% 0.20/0.46    spl2_10),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f146])).
% 0.20/0.46  fof(f146,plain,(
% 0.20/0.46    $false | spl2_10),
% 0.20/0.46    inference(resolution,[],[f145,f37])).
% 0.20/0.46  fof(f145,plain,(
% 0.20/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_10),
% 0.20/0.46    inference(resolution,[],[f139,f51])).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f137])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    spl2_1 | spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f38,f63,f59])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f33])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (13711)------------------------------
% 0.20/0.46  % (13711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (13711)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (13711)Memory used [KB]: 6396
% 0.20/0.46  % (13711)Time elapsed: 0.044 s
% 0.20/0.46  % (13711)------------------------------
% 0.20/0.46  % (13711)------------------------------
% 0.20/0.46  % (13708)Success in time 0.1 s
%------------------------------------------------------------------------------
