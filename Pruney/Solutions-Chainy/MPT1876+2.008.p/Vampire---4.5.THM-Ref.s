%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:36 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  162 (1971 expanded)
%              Number of leaves         :   29 ( 557 expanded)
%              Depth                    :   22
%              Number of atoms          :  682 (13846 expanded)
%              Number of equality atoms :   44 ( 153 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f476,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f139,f385,f475])).

fof(f475,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f473,f450])).

fof(f450,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f449,f404])).

fof(f404,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f77,f78,f399,f397,f400,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f400,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f78,f79,f80,f132,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & v1_pre_topc(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & v1_pre_topc(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f132,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).

fof(f58,plain,
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

fof(f59,plain,
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

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f79,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f397,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f78,f79,f80,f132,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f399,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f78,f79,f80,f132,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f77,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f449,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f416,f137])).

fof(f137,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f416,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(superposition,[],[f104,f401])).

fof(f401,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f75,f76,f78,f79,f80,f132,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK2(X0,X1)) = X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f104,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f473,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f402,f86])).

fof(f86,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f402,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f78,f400,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f385,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f372,f162])).

fof(f162,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f75,f78,f152,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f152,plain,(
    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f148,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f148,plain,(
    r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f142,f143,f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f70,f71])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f143,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f80,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f142,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f79,f107])).

fof(f107,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f66,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f372,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),sK0)
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f75,f78,f133,f308])).

fof(f308,plain,
    ( ! [X21] :
        ( ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X21)
        | v2_tex_2(sK1,X21)
        | v2_struct_0(X21) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f307,f245])).

fof(f245,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X1)
        | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl5_2 ),
    inference(superposition,[],[f89,f210])).

fof(f210,plain,
    ( sK1 = u1_struct_0(k1_tex_2(sK0,sK3(sK1)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f205,f185])).

fof(f185,plain,
    ( sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f164,f179])).

fof(f179,plain,
    ( sK1 = k6_domain_1(sK1,sK3(sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f136,f79,f150,f171,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f171,plain,(
    ~ v1_xboole_0(k6_domain_1(sK1,sK3(sK1))) ),
    inference(superposition,[],[f123,f149])).

fof(f149,plain,(
    k2_tarski(sK3(sK1),sK3(sK1)) = k6_domain_1(sK1,sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f79,f145,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f109,f84])).

fof(f84,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f145,plain,(
    m1_subset_1(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f142,f108])).

fof(f123,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f83,f84])).

fof(f83,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f150,plain,(
    r1_tarski(k6_domain_1(sK1,sK3(sK1)),sK1) ),
    inference(backward_demodulation,[],[f144,f149])).

fof(f144,plain,(
    r1_tarski(k2_tarski(sK3(sK1),sK3(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f142,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f120,f84])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f136,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f164,plain,(
    k6_domain_1(sK1,sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) ),
    inference(forward_demodulation,[],[f163,f149])).

fof(f163,plain,(
    k2_tarski(sK3(sK1),sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) ),
    inference(unit_resulting_resolution,[],[f153,f152,f124])).

fof(f153,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f148,f106])).

fof(f106,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f205,plain,(
    k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = u1_struct_0(k1_tex_2(sK0,sK3(sK1))) ),
    inference(unit_resulting_resolution,[],[f75,f78,f152,f160,f161,f162,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

fof(f161,plain,(
    v1_pre_topc(k1_tex_2(sK0,sK3(sK1))) ),
    inference(unit_resulting_resolution,[],[f75,f78,f152,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f160,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK3(sK1))) ),
    inference(unit_resulting_resolution,[],[f75,f78,f152,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f307,plain,
    ( ! [X21] :
        ( v2_tex_2(sK1,X21)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X21) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f306,f160])).

fof(f306,plain,
    ( ! [X21] :
        ( v2_tex_2(sK1,X21)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X21)
        | v2_struct_0(k1_tex_2(sK0,sK3(sK1)))
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X21) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f263,f228])).

fof(f228,plain,(
    v1_tdlat_3(k1_tex_2(sK0,sK3(sK1))) ),
    inference(unit_resulting_resolution,[],[f75,f78,f162,f160,f158,f208,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_pre_topc(X1)
      | ~ v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc25_tex_2)).

fof(f208,plain,(
    v2_pre_topc(k1_tex_2(sK0,sK3(sK1))) ),
    inference(unit_resulting_resolution,[],[f76,f78,f162,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f158,plain,(
    v7_struct_0(k1_tex_2(sK0,sK3(sK1))) ),
    inference(unit_resulting_resolution,[],[f75,f78,f152,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f263,plain,
    ( ! [X21] :
        ( v2_tex_2(sK1,X21)
        | ~ v1_tdlat_3(k1_tex_2(sK0,sK3(sK1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X21)
        | v2_struct_0(k1_tex_2(sK0,sK3(sK1)))
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X21) )
    | ~ spl5_2 ),
    inference(superposition,[],[f128,f210])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f133,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f139,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f81,f135,f131])).

fof(f81,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f138,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f82,f135,f131])).

fof(f82,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:51:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (7196)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (7195)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (7204)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (7190)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (7193)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (7212)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (7212)Refutation not found, incomplete strategy% (7212)------------------------------
% 0.22/0.54  % (7212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7212)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7212)Memory used [KB]: 10746
% 0.22/0.54  % (7212)Time elapsed: 0.124 s
% 0.22/0.54  % (7212)------------------------------
% 0.22/0.54  % (7212)------------------------------
% 0.22/0.54  % (7191)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (7213)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (7209)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (7216)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (7192)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (7194)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (7192)Refutation not found, incomplete strategy% (7192)------------------------------
% 0.22/0.54  % (7192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7192)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7192)Memory used [KB]: 10746
% 0.22/0.54  % (7192)Time elapsed: 0.123 s
% 0.22/0.54  % (7192)------------------------------
% 0.22/0.54  % (7192)------------------------------
% 0.22/0.54  % (7205)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (7207)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (7219)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (7208)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (7201)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (7197)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (7199)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (7211)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (7200)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (7200)Refutation not found, incomplete strategy% (7200)------------------------------
% 0.22/0.56  % (7200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (7200)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (7200)Memory used [KB]: 10746
% 0.22/0.56  % (7200)Time elapsed: 0.149 s
% 0.22/0.56  % (7200)------------------------------
% 0.22/0.56  % (7200)------------------------------
% 0.22/0.56  % (7215)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (7203)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (7206)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (7198)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (7217)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (7198)Refutation not found, incomplete strategy% (7198)------------------------------
% 0.22/0.57  % (7198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (7198)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (7198)Memory used [KB]: 10746
% 0.22/0.57  % (7198)Time elapsed: 0.158 s
% 0.22/0.57  % (7198)------------------------------
% 0.22/0.57  % (7198)------------------------------
% 0.22/0.57  % (7214)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.52/0.58  % (7210)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.52/0.58  % (7218)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.75/0.59  % (7202)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.75/0.59  % (7216)Refutation found. Thanks to Tanya!
% 1.75/0.59  % SZS status Theorem for theBenchmark
% 1.75/0.59  % SZS output start Proof for theBenchmark
% 1.75/0.59  fof(f476,plain,(
% 1.75/0.59    $false),
% 1.75/0.59    inference(avatar_sat_refutation,[],[f138,f139,f385,f475])).
% 1.75/0.59  fof(f475,plain,(
% 1.75/0.59    ~spl5_1 | spl5_2),
% 1.75/0.59    inference(avatar_contradiction_clause,[],[f474])).
% 1.75/0.59  fof(f474,plain,(
% 1.75/0.59    $false | (~spl5_1 | spl5_2)),
% 1.75/0.59    inference(subsumption_resolution,[],[f473,f450])).
% 1.75/0.59  fof(f450,plain,(
% 1.75/0.59    ~l1_struct_0(sK2(sK0,sK1)) | (~spl5_1 | spl5_2)),
% 1.75/0.59    inference(subsumption_resolution,[],[f449,f404])).
% 1.75/0.59  fof(f404,plain,(
% 1.75/0.59    v7_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f76,f77,f78,f399,f397,f400,f98])).
% 1.75/0.59  fof(f98,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f41])).
% 1.75/0.59  fof(f41,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f40])).
% 1.75/0.59  fof(f40,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f16])).
% 1.75/0.59  fof(f16,axiom,(
% 1.75/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).
% 1.75/0.59  fof(f400,plain,(
% 1.75/0.59    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_1),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f76,f78,f79,f80,f132,f102])).
% 1.75/0.59  fof(f102,plain,(
% 1.75/0.59    ( ! [X0,X1] : (m1_pre_topc(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f64])).
% 1.75/0.59  fof(f64,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f63])).
% 1.75/0.59  fof(f63,plain,(
% 1.75/0.59    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & v1_pre_topc(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 1.75/0.59    introduced(choice_axiom,[])).
% 1.75/0.59  fof(f43,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f42])).
% 1.75/0.59  fof(f42,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f22])).
% 1.75/0.59  fof(f22,axiom,(
% 1.75/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 1.75/0.59  fof(f132,plain,(
% 1.75/0.59    v2_tex_2(sK1,sK0) | ~spl5_1),
% 1.75/0.59    inference(avatar_component_clause,[],[f131])).
% 1.75/0.59  fof(f131,plain,(
% 1.75/0.59    spl5_1 <=> v2_tex_2(sK1,sK0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.75/0.59  fof(f80,plain,(
% 1.75/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.75/0.59    inference(cnf_transformation,[],[f60])).
% 1.75/0.59  fof(f60,plain,(
% 1.75/0.59    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.75/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f59,f58])).
% 1.75/0.59  fof(f58,plain,(
% 1.75/0.59    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.75/0.59    introduced(choice_axiom,[])).
% 1.75/0.59  fof(f59,plain,(
% 1.75/0.59    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 1.75/0.59    introduced(choice_axiom,[])).
% 1.75/0.59  fof(f57,plain,(
% 1.75/0.59    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f56])).
% 1.75/0.59  fof(f56,plain,(
% 1.75/0.59    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.75/0.59    inference(nnf_transformation,[],[f26])).
% 1.75/0.59  fof(f26,plain,(
% 1.75/0.59    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f25])).
% 1.75/0.59  fof(f25,plain,(
% 1.75/0.59    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f24])).
% 1.75/0.59  fof(f24,negated_conjecture,(
% 1.75/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.75/0.59    inference(negated_conjecture,[],[f23])).
% 1.75/0.59  fof(f23,conjecture,(
% 1.75/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 1.75/0.59  fof(f79,plain,(
% 1.75/0.59    ~v1_xboole_0(sK1)),
% 1.75/0.59    inference(cnf_transformation,[],[f60])).
% 1.75/0.59  fof(f397,plain,(
% 1.75/0.59    ~v2_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f76,f78,f79,f80,f132,f99])).
% 1.75/0.59  fof(f99,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f64])).
% 1.75/0.59  fof(f399,plain,(
% 1.75/0.59    v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_1),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f76,f78,f79,f80,f132,f101])).
% 1.75/0.59  fof(f101,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f64])).
% 1.75/0.59  fof(f78,plain,(
% 1.75/0.59    l1_pre_topc(sK0)),
% 1.75/0.59    inference(cnf_transformation,[],[f60])).
% 1.75/0.59  fof(f77,plain,(
% 1.75/0.59    v2_tdlat_3(sK0)),
% 1.75/0.59    inference(cnf_transformation,[],[f60])).
% 1.75/0.59  fof(f76,plain,(
% 1.75/0.59    v2_pre_topc(sK0)),
% 1.75/0.59    inference(cnf_transformation,[],[f60])).
% 1.75/0.59  fof(f75,plain,(
% 1.75/0.59    ~v2_struct_0(sK0)),
% 1.75/0.59    inference(cnf_transformation,[],[f60])).
% 1.75/0.59  fof(f449,plain,(
% 1.75/0.59    ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | (~spl5_1 | spl5_2)),
% 1.75/0.59    inference(subsumption_resolution,[],[f416,f137])).
% 1.75/0.59  fof(f137,plain,(
% 1.75/0.59    ~v1_zfmisc_1(sK1) | spl5_2),
% 1.75/0.59    inference(avatar_component_clause,[],[f135])).
% 1.75/0.59  fof(f135,plain,(
% 1.75/0.59    spl5_2 <=> v1_zfmisc_1(sK1)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.75/0.59  fof(f416,plain,(
% 1.75/0.59    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 1.75/0.59    inference(superposition,[],[f104,f401])).
% 1.75/0.59  fof(f401,plain,(
% 1.75/0.59    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f76,f78,f79,f80,f132,f103])).
% 1.75/0.59  fof(f103,plain,(
% 1.75/0.59    ( ! [X0,X1] : (u1_struct_0(sK2(X0,X1)) = X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f64])).
% 1.75/0.59  fof(f104,plain,(
% 1.75/0.59    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f45])).
% 1.75/0.59  fof(f45,plain,(
% 1.75/0.59    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f44])).
% 1.75/0.59  fof(f44,plain,(
% 1.75/0.59    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f11])).
% 1.75/0.59  fof(f11,axiom,(
% 1.75/0.59    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.75/0.59  fof(f473,plain,(
% 1.75/0.59    l1_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f402,f86])).
% 1.75/0.59  fof(f86,plain,(
% 1.75/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f29])).
% 1.75/0.59  fof(f29,plain,(
% 1.75/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.75/0.59    inference(ennf_transformation,[],[f9])).
% 1.75/0.59  fof(f9,axiom,(
% 1.75/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.75/0.59  fof(f402,plain,(
% 1.75/0.59    l1_pre_topc(sK2(sK0,sK1)) | ~spl5_1),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f78,f400,f88])).
% 1.75/0.59  fof(f88,plain,(
% 1.75/0.59    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f32])).
% 1.75/0.59  fof(f32,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.75/0.59    inference(ennf_transformation,[],[f10])).
% 1.75/0.59  fof(f10,axiom,(
% 1.75/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.75/0.59  fof(f385,plain,(
% 1.75/0.59    spl5_1 | ~spl5_2),
% 1.75/0.59    inference(avatar_contradiction_clause,[],[f384])).
% 1.75/0.59  fof(f384,plain,(
% 1.75/0.59    $false | (spl5_1 | ~spl5_2)),
% 1.75/0.59    inference(subsumption_resolution,[],[f372,f162])).
% 1.75/0.59  fof(f162,plain,(
% 1.75/0.59    m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),sK0)),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f78,f152,f115])).
% 1.75/0.59  fof(f115,plain,(
% 1.75/0.59    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f54])).
% 1.75/0.59  fof(f54,plain,(
% 1.75/0.59    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f53])).
% 1.75/0.59  fof(f53,plain,(
% 1.75/0.59    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f18])).
% 1.75/0.59  fof(f18,axiom,(
% 1.75/0.59    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 1.75/0.59  fof(f152,plain,(
% 1.75/0.59    m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f148,f108])).
% 1.75/0.59  fof(f108,plain,(
% 1.75/0.59    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f48])).
% 1.75/0.59  fof(f48,plain,(
% 1.75/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.75/0.59    inference(ennf_transformation,[],[f6])).
% 1.75/0.59  fof(f6,axiom,(
% 1.75/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.75/0.59  fof(f148,plain,(
% 1.75/0.59    r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f142,f143,f116])).
% 1.75/0.59  fof(f116,plain,(
% 1.75/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f72])).
% 1.75/0.59  fof(f72,plain,(
% 1.75/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.75/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f70,f71])).
% 1.75/0.59  fof(f71,plain,(
% 1.75/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.75/0.59    introduced(choice_axiom,[])).
% 1.75/0.59  fof(f70,plain,(
% 1.75/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.75/0.59    inference(rectify,[],[f69])).
% 1.75/0.59  fof(f69,plain,(
% 1.75/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.75/0.59    inference(nnf_transformation,[],[f55])).
% 1.75/0.59  fof(f55,plain,(
% 1.75/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f2])).
% 1.75/0.59  fof(f2,axiom,(
% 1.75/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.75/0.59  fof(f143,plain,(
% 1.75/0.59    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f80,f121])).
% 1.75/0.59  fof(f121,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f74])).
% 1.75/0.59  fof(f74,plain,(
% 1.75/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.75/0.59    inference(nnf_transformation,[],[f7])).
% 1.75/0.59  fof(f7,axiom,(
% 1.75/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.75/0.59  fof(f142,plain,(
% 1.75/0.59    r2_hidden(sK3(sK1),sK1)),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f79,f107])).
% 1.75/0.59  fof(f107,plain,(
% 1.75/0.59    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f68])).
% 1.75/0.59  fof(f68,plain,(
% 1.75/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.75/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f66,f67])).
% 1.75/0.59  fof(f67,plain,(
% 1.75/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.75/0.59    introduced(choice_axiom,[])).
% 1.75/0.59  fof(f66,plain,(
% 1.75/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.75/0.59    inference(rectify,[],[f65])).
% 1.75/0.59  fof(f65,plain,(
% 1.75/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.75/0.59    inference(nnf_transformation,[],[f1])).
% 1.75/0.59  fof(f1,axiom,(
% 1.75/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.75/0.59  fof(f372,plain,(
% 1.75/0.59    ~m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),sK0) | (spl5_1 | ~spl5_2)),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f78,f133,f308])).
% 1.75/0.59  fof(f308,plain,(
% 1.75/0.59    ( ! [X21] : (~l1_pre_topc(X21) | ~m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X21) | v2_tex_2(sK1,X21) | v2_struct_0(X21)) ) | ~spl5_2),
% 1.75/0.59    inference(subsumption_resolution,[],[f307,f245])).
% 1.75/0.59  fof(f245,plain,(
% 1.75/0.59    ( ! [X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X1) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))) ) | ~spl5_2),
% 1.75/0.59    inference(superposition,[],[f89,f210])).
% 1.75/0.59  fof(f210,plain,(
% 1.75/0.59    sK1 = u1_struct_0(k1_tex_2(sK0,sK3(sK1))) | ~spl5_2),
% 1.75/0.59    inference(forward_demodulation,[],[f205,f185])).
% 1.75/0.59  fof(f185,plain,(
% 1.75/0.59    sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | ~spl5_2),
% 1.75/0.59    inference(backward_demodulation,[],[f164,f179])).
% 1.75/0.59  fof(f179,plain,(
% 1.75/0.59    sK1 = k6_domain_1(sK1,sK3(sK1)) | ~spl5_2),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f136,f79,f150,f171,f85])).
% 1.75/0.59  fof(f85,plain,(
% 1.75/0.59    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f28])).
% 1.75/0.59  fof(f28,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.75/0.59    inference(flattening,[],[f27])).
% 1.75/0.59  fof(f27,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.75/0.59    inference(ennf_transformation,[],[f20])).
% 1.75/0.59  fof(f20,axiom,(
% 1.75/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.75/0.59  fof(f171,plain,(
% 1.75/0.59    ~v1_xboole_0(k6_domain_1(sK1,sK3(sK1)))),
% 1.75/0.59    inference(superposition,[],[f123,f149])).
% 1.75/0.59  fof(f149,plain,(
% 1.75/0.59    k2_tarski(sK3(sK1),sK3(sK1)) = k6_domain_1(sK1,sK3(sK1))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f79,f145,f124])).
% 1.75/0.59  fof(f124,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f109,f84])).
% 1.75/0.59  fof(f84,plain,(
% 1.75/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f3])).
% 1.75/0.59  fof(f3,axiom,(
% 1.75/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.75/0.59  fof(f109,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f50])).
% 1.75/0.59  fof(f50,plain,(
% 1.75/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.75/0.59    inference(flattening,[],[f49])).
% 1.75/0.59  fof(f49,plain,(
% 1.75/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f12])).
% 1.75/0.59  fof(f12,axiom,(
% 1.75/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.75/0.59  fof(f145,plain,(
% 1.75/0.59    m1_subset_1(sK3(sK1),sK1)),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f142,f108])).
% 1.75/0.59  fof(f123,plain,(
% 1.75/0.59    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 1.75/0.59    inference(definition_unfolding,[],[f83,f84])).
% 1.75/0.59  fof(f83,plain,(
% 1.75/0.59    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.75/0.59    inference(cnf_transformation,[],[f4])).
% 1.75/0.59  fof(f4,axiom,(
% 1.75/0.59    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.75/0.59  fof(f150,plain,(
% 1.75/0.59    r1_tarski(k6_domain_1(sK1,sK3(sK1)),sK1)),
% 1.75/0.59    inference(backward_demodulation,[],[f144,f149])).
% 1.75/0.59  fof(f144,plain,(
% 1.75/0.59    r1_tarski(k2_tarski(sK3(sK1),sK3(sK1)),sK1)),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f142,f125])).
% 1.75/0.59  fof(f125,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.75/0.59    inference(definition_unfolding,[],[f120,f84])).
% 1.75/0.59  fof(f120,plain,(
% 1.75/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f73])).
% 1.75/0.59  fof(f73,plain,(
% 1.75/0.59    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.75/0.59    inference(nnf_transformation,[],[f5])).
% 1.75/0.59  fof(f5,axiom,(
% 1.75/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.75/0.59  fof(f136,plain,(
% 1.75/0.59    v1_zfmisc_1(sK1) | ~spl5_2),
% 1.75/0.59    inference(avatar_component_clause,[],[f135])).
% 1.75/0.59  fof(f164,plain,(
% 1.75/0.59    k6_domain_1(sK1,sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))),
% 1.75/0.59    inference(forward_demodulation,[],[f163,f149])).
% 1.75/0.59  fof(f163,plain,(
% 1.75/0.59    k2_tarski(sK3(sK1),sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f153,f152,f124])).
% 1.75/0.59  fof(f153,plain,(
% 1.75/0.59    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f148,f106])).
% 1.75/0.59  fof(f106,plain,(
% 1.75/0.59    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f68])).
% 1.75/0.59  fof(f205,plain,(
% 1.75/0.59    k6_domain_1(u1_struct_0(sK0),sK3(sK1)) = u1_struct_0(k1_tex_2(sK0,sK3(sK1)))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f78,f152,f160,f161,f162,f127])).
% 1.75/0.59  fof(f127,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(equality_resolution,[],[f93])).
% 1.75/0.59  fof(f93,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f61])).
% 1.75/0.59  fof(f61,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(nnf_transformation,[],[f37])).
% 1.75/0.59  fof(f37,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f36])).
% 1.75/0.59  fof(f36,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f17])).
% 1.75/0.59  fof(f17,axiom,(
% 1.75/0.59    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).
% 1.75/0.59  fof(f161,plain,(
% 1.75/0.59    v1_pre_topc(k1_tex_2(sK0,sK3(sK1)))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f78,f152,f114])).
% 1.75/0.59  fof(f114,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f54])).
% 1.75/0.59  fof(f160,plain,(
% 1.75/0.59    ~v2_struct_0(k1_tex_2(sK0,sK3(sK1)))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f78,f152,f113])).
% 1.75/0.59  fof(f113,plain,(
% 1.75/0.59    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f54])).
% 1.75/0.59  fof(f89,plain,(
% 1.75/0.59    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f33])).
% 1.75/0.59  fof(f33,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.75/0.59    inference(ennf_transformation,[],[f13])).
% 1.75/0.59  fof(f13,axiom,(
% 1.75/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.75/0.59  fof(f307,plain,(
% 1.75/0.59    ( ! [X21] : (v2_tex_2(sK1,X21) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X21))) | ~m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X21) | ~l1_pre_topc(X21) | v2_struct_0(X21)) ) | ~spl5_2),
% 1.75/0.59    inference(subsumption_resolution,[],[f306,f160])).
% 1.75/0.59  fof(f306,plain,(
% 1.75/0.59    ( ! [X21] : (v2_tex_2(sK1,X21) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X21))) | ~m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X21) | v2_struct_0(k1_tex_2(sK0,sK3(sK1))) | ~l1_pre_topc(X21) | v2_struct_0(X21)) ) | ~spl5_2),
% 1.75/0.59    inference(subsumption_resolution,[],[f263,f228])).
% 1.75/0.59  fof(f228,plain,(
% 1.75/0.59    v1_tdlat_3(k1_tex_2(sK0,sK3(sK1)))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f78,f162,f160,f158,f208,f91])).
% 1.75/0.59  fof(f91,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f35])).
% 1.75/0.59  fof(f35,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : ((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f34])).
% 1.75/0.59  fof(f34,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f14])).
% 1.75/0.59  fof(f14,axiom,(
% 1.75/0.59    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc25_tex_2)).
% 1.75/0.59  fof(f208,plain,(
% 1.75/0.59    v2_pre_topc(k1_tex_2(sK0,sK3(sK1)))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f76,f78,f162,f105])).
% 1.75/0.59  fof(f105,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f47])).
% 1.75/0.59  fof(f47,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.75/0.59    inference(flattening,[],[f46])).
% 1.75/0.59  fof(f46,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f8])).
% 1.75/0.59  fof(f8,axiom,(
% 1.75/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.75/0.59  fof(f158,plain,(
% 1.75/0.59    v7_struct_0(k1_tex_2(sK0,sK3(sK1)))),
% 1.75/0.59    inference(unit_resulting_resolution,[],[f75,f78,f152,f111])).
% 1.75/0.59  fof(f111,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f52])).
% 1.75/0.59  fof(f52,plain,(
% 1.75/0.59    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f51])).
% 1.75/0.59  fof(f51,plain,(
% 1.75/0.59    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f19])).
% 1.75/0.59  fof(f19,axiom,(
% 1.75/0.59    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 1.75/0.59  fof(f263,plain,(
% 1.75/0.59    ( ! [X21] : (v2_tex_2(sK1,X21) | ~v1_tdlat_3(k1_tex_2(sK0,sK3(sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X21))) | ~m1_pre_topc(k1_tex_2(sK0,sK3(sK1)),X21) | v2_struct_0(k1_tex_2(sK0,sK3(sK1))) | ~l1_pre_topc(X21) | v2_struct_0(X21)) ) | ~spl5_2),
% 1.75/0.59    inference(superposition,[],[f128,f210])).
% 1.75/0.59  fof(f128,plain,(
% 1.75/0.59    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(equality_resolution,[],[f96])).
% 1.75/0.59  fof(f96,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f62])).
% 1.75/0.59  fof(f62,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(nnf_transformation,[],[f39])).
% 1.75/0.59  fof(f39,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.75/0.59    inference(flattening,[],[f38])).
% 1.75/0.59  fof(f38,plain,(
% 1.75/0.59    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.75/0.59    inference(ennf_transformation,[],[f21])).
% 1.75/0.59  fof(f21,axiom,(
% 1.75/0.59    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 1.75/0.59  fof(f133,plain,(
% 1.75/0.59    ~v2_tex_2(sK1,sK0) | spl5_1),
% 1.75/0.59    inference(avatar_component_clause,[],[f131])).
% 1.75/0.59  fof(f139,plain,(
% 1.75/0.59    spl5_1 | spl5_2),
% 1.75/0.59    inference(avatar_split_clause,[],[f81,f135,f131])).
% 1.75/0.59  fof(f81,plain,(
% 1.75/0.59    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 1.75/0.59    inference(cnf_transformation,[],[f60])).
% 1.75/0.59  fof(f138,plain,(
% 1.75/0.59    ~spl5_1 | ~spl5_2),
% 1.75/0.59    inference(avatar_split_clause,[],[f82,f135,f131])).
% 1.75/0.59  fof(f82,plain,(
% 1.75/0.59    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 1.75/0.59    inference(cnf_transformation,[],[f60])).
% 1.75/0.59  % SZS output end Proof for theBenchmark
% 1.75/0.59  % (7216)------------------------------
% 1.75/0.59  % (7216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.59  % (7216)Termination reason: Refutation
% 1.75/0.59  
% 1.75/0.59  % (7216)Memory used [KB]: 11001
% 1.75/0.59  % (7216)Time elapsed: 0.180 s
% 1.75/0.59  % (7216)------------------------------
% 1.75/0.59  % (7216)------------------------------
% 1.75/0.60  % (7189)Success in time 0.228 s
%------------------------------------------------------------------------------
