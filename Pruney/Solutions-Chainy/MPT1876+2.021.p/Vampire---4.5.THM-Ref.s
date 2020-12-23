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
% DateTime   : Thu Dec  3 13:21:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 933 expanded)
%              Number of leaves         :   30 ( 261 expanded)
%              Depth                    :   23
%              Number of atoms          :  781 (7407 expanded)
%              Number of equality atoms :   45 ( 111 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f467,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f104,f266,f303,f356,f365,f374,f383,f392,f466])).

fof(f466,plain,
    ( spl5_2
    | ~ spl5_24
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | spl5_2
    | ~ spl5_24
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f464,f408])).

fof(f408,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f401,f66])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f401,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_25 ),
    inference(resolution,[],[f373,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f373,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl5_25
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f464,plain,
    ( ~ l1_pre_topc(sK2(sK0,sK1))
    | spl5_2
    | ~ spl5_24
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(resolution,[],[f461,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f461,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | spl5_2
    | ~ spl5_24
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f460,f407])).

fof(f407,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f406,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f406,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f405,f64])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f405,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f404,f65])).

fof(f65,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f404,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f403,f66])).

fof(f403,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_25
    | ~ spl5_26
    | spl5_27 ),
    inference(subsumption_resolution,[],[f402,f382])).

fof(f382,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl5_26
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f402,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_25
    | spl5_27 ),
    inference(subsumption_resolution,[],[f400,f391])).

fof(f391,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl5_27
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f400,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_25 ),
    inference(resolution,[],[f373,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ v1_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f460,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | spl5_2
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f418,f102])).

fof(f102,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f418,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_24 ),
    inference(superposition,[],[f88,f364])).

fof(f364,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl5_24
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f88,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f392,plain,
    ( ~ spl5_27
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f387,f96,f389])).

fof(f96,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f387,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f386,f63])).

fof(f386,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f385,f64])).

fof(f385,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f384,f66])).

fof(f384,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f106,f67])).

fof(f67,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f106,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK2(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f383,plain,
    ( spl5_26
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f378,f96,f380])).

fof(f378,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f377,f63])).

fof(f377,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f376,f64])).

fof(f376,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f375,f66])).

fof(f375,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f107,f67])).

fof(f107,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK2(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f374,plain,
    ( spl5_25
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f369,f96,f371])).

fof(f369,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f368,f63])).

fof(f368,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f367,f64])).

fof(f367,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f366,f66])).

fof(f366,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f108,f67])).

fof(f108,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK2(X0,X1),X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f365,plain,
    ( spl5_24
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f360,f96,f362])).

fof(f360,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f359,f63])).

fof(f359,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f358,f64])).

fof(f358,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f357,f66])).

fof(f357,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f67])).

fof(f109,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK2(X0,X1)) = X1
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f356,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f345,f98])).

fof(f98,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f345,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f265,f343])).

fof(f343,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f342,f71])).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f342,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | v1_xboole_0(k1_tarski(sK4(sK1)))
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f341,f67])).

fof(f341,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | v1_xboole_0(sK1)
    | v1_xboole_0(k1_tarski(sK4(sK1)))
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f340,f101])).

fof(f101,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f340,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(k1_tarski(sK4(sK1)))
    | ~ spl5_18 ),
    inference(resolution,[],[f317,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f317,plain,
    ( r1_tarski(k1_tarski(sK4(sK1)),sK1)
    | ~ spl5_18 ),
    inference(resolution,[],[f314,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f314,plain,
    ( m1_subset_1(k1_tarski(sK4(sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_18 ),
    inference(backward_demodulation,[],[f312,f313])).

fof(f313,plain,
    ( k1_tarski(sK4(sK1)) = k6_domain_1(sK1,sK4(sK1))
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f311,f67])).

fof(f311,plain,
    ( k1_tarski(sK4(sK1)) = k6_domain_1(sK1,sK4(sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_18 ),
    inference(resolution,[],[f260,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f260,plain,
    ( m1_subset_1(sK4(sK1),sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl5_18
  <=> m1_subset_1(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f312,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK4(sK1)),k1_zfmisc_1(sK1))
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f310,f67])).

fof(f310,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK4(sK1)),k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_18 ),
    inference(resolution,[],[f260,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f265,plain,
    ( v2_tex_2(k1_tarski(sK4(sK1)),sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl5_19
  <=> v2_tex_2(k1_tarski(sK4(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f303,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl5_18 ),
    inference(subsumption_resolution,[],[f301,f105])).

fof(f105,plain,(
    r2_hidden(sK4(sK1),sK1) ),
    inference(resolution,[],[f67,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f301,plain,
    ( ~ r2_hidden(sK4(sK1),sK1)
    | spl5_18 ),
    inference(resolution,[],[f261,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f261,plain,
    ( ~ m1_subset_1(sK4(sK1),sK1)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f259])).

fof(f266,plain,
    ( ~ spl5_18
    | spl5_19 ),
    inference(avatar_split_clause,[],[f257,f263,f259])).

fof(f257,plain,
    ( v2_tex_2(k1_tarski(sK4(sK1)),sK0)
    | ~ m1_subset_1(sK4(sK1),sK1) ),
    inference(superposition,[],[f252,f256])).

fof(f256,plain,(
    k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1)) ),
    inference(resolution,[],[f255,f105])).

fof(f255,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    inference(resolution,[],[f254,f91])).

fof(f254,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | k6_domain_1(u1_struct_0(sK0),X4) = k1_tarski(X4) ) ),
    inference(subsumption_resolution,[],[f248,f126])).

fof(f126,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f114,f67])).

fof(f114,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f248,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | k6_domain_1(u1_struct_0(sK0),X4) = k1_tarski(X4)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f244,f92])).

fof(f244,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f243,f63])).

fof(f243,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f242,f66])).

fof(f242,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f235,f122])).

fof(f122,plain,(
    m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f121,f63])).

fof(f121,plain,
    ( m1_pre_topc(sK3(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f120,f66])).

fof(f120,plain,
    ( m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f111,f67])).

fof(f111,plain,
    ( m1_pre_topc(sK3(sK0,sK1),sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK3(X0,X1),X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK3(X0,X1)) = X1
            & m1_pre_topc(sK3(X0,X1),X0)
            & ~ v2_struct_0(sK3(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X1
        & m1_pre_topc(sK3(X0,X1),X0)
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f235,plain,(
    ! [X8,X9] :
      ( ~ m1_pre_topc(sK3(sK0,sK1),X9)
      | m1_subset_1(X8,u1_struct_0(X9))
      | ~ m1_subset_1(X8,sK1)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f193,f119])).

fof(f119,plain,(
    ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f118,f63])).

fof(f118,plain,
    ( ~ v2_struct_0(sK3(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f66])).

fof(f117,plain,
    ( ~ v2_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f110,f67])).

fof(f110,plain,
    ( ~ v2_struct_0(sK3(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK3(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f193,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,sK1)
      | m1_subset_1(X8,u1_struct_0(X9))
      | ~ m1_pre_topc(sK3(sK0,sK1),X9)
      | v2_struct_0(sK3(sK0,sK1))
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X9) ) ),
    inference(superposition,[],[f87,f125])).

fof(f125,plain,(
    sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f124,f63])).

fof(f124,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f123,f66])).

fof(f123,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f112,f67])).

fof(f112,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK3(X0,X1)) = X1
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f252,plain,(
    ! [X2] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X2),sK0)
      | ~ m1_subset_1(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f251,f63])).

fof(f251,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK1)
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X2),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f250,f64])).

fof(f250,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK1)
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X2),sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f246,f66])).

fof(f246,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK1)
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X2),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f244,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f104,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f69,f100,f96])).

fof(f69,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f103,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f70,f100,f96])).

fof(f70,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (21855)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.46  % (21848)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.47  % (21860)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.48  % (21875)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.48  % (21855)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f467,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f103,f104,f266,f303,f356,f365,f374,f383,f392,f466])).
% 0.21/0.48  fof(f466,plain,(
% 0.21/0.48    spl5_2 | ~spl5_24 | ~spl5_25 | ~spl5_26 | spl5_27),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f465])).
% 0.21/0.48  fof(f465,plain,(
% 0.21/0.48    $false | (spl5_2 | ~spl5_24 | ~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f464,f408])).
% 0.21/0.48  fof(f408,plain,(
% 0.21/0.48    l1_pre_topc(sK2(sK0,sK1)) | ~spl5_25),
% 0.21/0.48    inference(subsumption_resolution,[],[f401,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f18])).
% 0.21/0.48  fof(f18,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.48  fof(f401,plain,(
% 0.21/0.48    l1_pre_topc(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl5_25),
% 0.21/0.48    inference(resolution,[],[f373,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f371])).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    spl5_25 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.48  fof(f464,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2(sK0,sK1)) | (spl5_2 | ~spl5_24 | ~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.48    inference(resolution,[],[f461,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f461,plain,(
% 0.21/0.48    ~l1_struct_0(sK2(sK0,sK1)) | (spl5_2 | ~spl5_24 | ~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f460,f407])).
% 0.21/0.48  fof(f407,plain,(
% 0.21/0.48    v7_struct_0(sK2(sK0,sK1)) | (~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f406,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f54])).
% 0.21/0.48  fof(f406,plain,(
% 0.21/0.48    v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f405,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f54])).
% 0.21/0.48  fof(f405,plain,(
% 0.21/0.48    v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f404,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    v2_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f54])).
% 0.21/0.48  fof(f404,plain,(
% 0.21/0.48    v7_struct_0(sK2(sK0,sK1)) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f403,f66])).
% 0.21/0.48  fof(f403,plain,(
% 0.21/0.48    v7_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_25 | ~spl5_26 | spl5_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f402,f382])).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f380])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    spl5_26 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.48  fof(f402,plain,(
% 0.21/0.48    v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_25 | spl5_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f400,f391])).
% 0.21/0.48  fof(f391,plain,(
% 0.21/0.48    ~v2_struct_0(sK2(sK0,sK1)) | spl5_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f389])).
% 0.21/0.48  fof(f389,plain,(
% 0.21/0.48    spl5_27 <=> v2_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.48  fof(f400,plain,(
% 0.21/0.48    v7_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_25),
% 0.21/0.48    inference(resolution,[],[f373,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v7_struct_0(X1) | v2_struct_0(X1) | ~v1_tdlat_3(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.21/0.48  fof(f460,plain,(
% 0.21/0.48    ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | (spl5_2 | ~spl5_24)),
% 0.21/0.48    inference(subsumption_resolution,[],[f418,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl5_2 <=> v1_zfmisc_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f418,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~spl5_24),
% 0.21/0.48    inference(superposition,[],[f88,f364])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f362])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    spl5_24 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.48  fof(f392,plain,(
% 0.21/0.48    ~spl5_27 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f387,f96,f389])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl5_1 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f387,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f386,f63])).
% 0.21/0.48  fof(f386,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f385,f64])).
% 0.21/0.48  fof(f385,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f384,f66])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f54])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f68,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v2_struct_0(sK2(X0,X1)) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f54])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    spl5_26 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f378,f96,f380])).
% 0.21/0.48  fof(f378,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f377,f63])).
% 0.21/0.48  fof(f377,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f376,f64])).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f375,f66])).
% 0.21/0.48  fof(f375,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f107,f67])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f68,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK2(X0,X1)) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f56])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    spl5_25 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f369,f96,f371])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f368,f63])).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f367,f64])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f366,f66])).
% 0.21/0.48  fof(f366,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f108,f67])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK2(sK0,sK1),sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f68,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK2(X0,X1),X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f56])).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    spl5_24 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f360,f96,f362])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f359,f63])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f358,f64])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f357,f66])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f109,f67])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f68,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | u1_struct_0(sK2(X0,X1)) = X1 | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f56])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    spl5_1 | ~spl5_2 | ~spl5_18 | ~spl5_19),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f355])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    $false | (spl5_1 | ~spl5_2 | ~spl5_18 | ~spl5_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f345,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    v2_tex_2(sK1,sK0) | (~spl5_2 | ~spl5_18 | ~spl5_19)),
% 0.21/0.48    inference(backward_demodulation,[],[f265,f343])).
% 0.21/0.48  fof(f343,plain,(
% 0.21/0.48    sK1 = k1_tarski(sK4(sK1)) | (~spl5_2 | ~spl5_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f342,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    sK1 = k1_tarski(sK4(sK1)) | v1_xboole_0(k1_tarski(sK4(sK1))) | (~spl5_2 | ~spl5_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f341,f67])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    sK1 = k1_tarski(sK4(sK1)) | v1_xboole_0(sK1) | v1_xboole_0(k1_tarski(sK4(sK1))) | (~spl5_2 | ~spl5_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f340,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    sK1 = k1_tarski(sK4(sK1)) | ~v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | v1_xboole_0(k1_tarski(sK4(sK1))) | ~spl5_18),
% 0.21/0.48    inference(resolution,[],[f317,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.48  fof(f317,plain,(
% 0.21/0.48    r1_tarski(k1_tarski(sK4(sK1)),sK1) | ~spl5_18),
% 0.21/0.48    inference(resolution,[],[f314,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f314,plain,(
% 0.21/0.48    m1_subset_1(k1_tarski(sK4(sK1)),k1_zfmisc_1(sK1)) | ~spl5_18),
% 0.21/0.48    inference(backward_demodulation,[],[f312,f313])).
% 0.21/0.48  fof(f313,plain,(
% 0.21/0.48    k1_tarski(sK4(sK1)) = k6_domain_1(sK1,sK4(sK1)) | ~spl5_18),
% 0.21/0.48    inference(subsumption_resolution,[],[f311,f67])).
% 0.21/0.48  fof(f311,plain,(
% 0.21/0.48    k1_tarski(sK4(sK1)) = k6_domain_1(sK1,sK4(sK1)) | v1_xboole_0(sK1) | ~spl5_18),
% 0.21/0.48    inference(resolution,[],[f260,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    m1_subset_1(sK4(sK1),sK1) | ~spl5_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f259])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    spl5_18 <=> m1_subset_1(sK4(sK1),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.48  fof(f312,plain,(
% 0.21/0.48    m1_subset_1(k6_domain_1(sK1,sK4(sK1)),k1_zfmisc_1(sK1)) | ~spl5_18),
% 0.21/0.48    inference(subsumption_resolution,[],[f310,f67])).
% 0.21/0.48  fof(f310,plain,(
% 0.21/0.48    m1_subset_1(k6_domain_1(sK1,sK4(sK1)),k1_zfmisc_1(sK1)) | v1_xboole_0(sK1) | ~spl5_18),
% 0.21/0.48    inference(resolution,[],[f260,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    v2_tex_2(k1_tarski(sK4(sK1)),sK0) | ~spl5_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f263])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    spl5_19 <=> v2_tex_2(k1_tarski(sK4(sK1)),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    spl5_18),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f302])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    $false | spl5_18),
% 0.21/0.48    inference(subsumption_resolution,[],[f301,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    r2_hidden(sK4(sK1),sK1)),
% 0.21/0.48    inference(resolution,[],[f67,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f60,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(rectify,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    ~r2_hidden(sK4(sK1),sK1) | spl5_18),
% 0.21/0.48    inference(resolution,[],[f261,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    ~m1_subset_1(sK4(sK1),sK1) | spl5_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f259])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    ~spl5_18 | spl5_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f257,f263,f259])).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    v2_tex_2(k1_tarski(sK4(sK1)),sK0) | ~m1_subset_1(sK4(sK1),sK1)),
% 0.21/0.48    inference(superposition,[],[f252,f256])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    k1_tarski(sK4(sK1)) = k6_domain_1(u1_struct_0(sK0),sK4(sK1))),
% 0.21/0.48    inference(resolution,[],[f255,f105])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0)) )),
% 0.21/0.48    inference(resolution,[],[f254,f91])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_subset_1(X4,sK1) | k6_domain_1(u1_struct_0(sK0),X4) = k1_tarski(X4)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f248,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f67])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.48    inference(resolution,[],[f68,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    ( ! [X4] : (~m1_subset_1(X4,sK1) | k6_domain_1(u1_struct_0(sK0),X4) = k1_tarski(X4) | v1_xboole_0(u1_struct_0(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f244,f92])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f243,f63])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,sK1) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f242,f66])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f235,f122])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f121,f63])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    m1_pre_topc(sK3(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f66])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    m1_pre_topc(sK3(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f67])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    m1_pre_topc(sK3(sK0,sK1),sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f68,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK3(X0,X1),X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & ~v2_struct_0(sK3(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X1 & m1_pre_topc(sK3(X0,X1),X0) & ~v2_struct_0(sK3(X0,X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ( ! [X8,X9] : (~m1_pre_topc(sK3(sK0,sK1),X9) | m1_subset_1(X8,u1_struct_0(X9)) | ~m1_subset_1(X8,sK1) | ~l1_pre_topc(X9) | v2_struct_0(X9)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f193,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ~v2_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f63])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~v2_struct_0(sK3(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f66])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f67])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~v2_struct_0(sK3(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f68,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK3(X0,X1)) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f58])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ( ! [X8,X9] : (~m1_subset_1(X8,sK1) | m1_subset_1(X8,u1_struct_0(X9)) | ~m1_pre_topc(sK3(sK0,sK1),X9) | v2_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(X9) | v2_struct_0(X9)) )),
% 0.21/0.48    inference(superposition,[],[f87,f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f63])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK3(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f66])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK3(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f67])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK3(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f68,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK3(X0,X1)) = X1 | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f58])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ( ! [X2] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X2),sK0) | ~m1_subset_1(X2,sK1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f251,f63])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,sK1) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X2),sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f250,f64])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,sK1) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X2),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f246,f66])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,sK1) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.48    inference(resolution,[],[f244,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl5_1 | spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f69,f100,f96])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f54])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f70,f100,f96])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f54])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21855)------------------------------
% 0.21/0.48  % (21855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21855)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21855)Memory used [KB]: 10874
% 0.21/0.48  % (21855)Time elapsed: 0.072 s
% 0.21/0.48  % (21855)------------------------------
% 0.21/0.48  % (21855)------------------------------
% 0.21/0.49  % (21846)Success in time 0.135 s
%------------------------------------------------------------------------------
