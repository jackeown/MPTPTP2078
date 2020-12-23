%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 276 expanded)
%              Number of leaves         :   35 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  543 (1124 expanded)
%              Number of equality atoms :   23 (  47 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f85,f89,f93,f97,f114,f118,f151,f156,f165,f174,f177,f186,f194,f211,f218,f222,f225,f227,f277,f278])).

fof(f278,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f277,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f276,f220,f87,f80])).

fof(f80,plain,
    ( spl3_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f87,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f220,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f276,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(resolution,[],[f221,f88])).

fof(f88,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f227,plain,
    ( spl3_5
    | ~ spl3_26
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f226,f189,f216,f95])).

fof(f95,plain,
    ( spl3_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f216,plain,
    ( spl3_26
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f189,plain,
    ( spl3_21
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f226,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_21 ),
    inference(resolution,[],[f190,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f190,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f189])).

fof(f225,plain,
    ( ~ spl3_4
    | spl3_26 ),
    inference(avatar_split_clause,[],[f224,f216,f91])).

fof(f91,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f224,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_26 ),
    inference(resolution,[],[f217,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f217,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_26 ),
    inference(avatar_component_clause,[],[f216])).

fof(f222,plain,
    ( spl3_21
    | spl3_27
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f213,f192,f220,f189])).

fof(f192,plain,
    ( spl3_22
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl3_22 ),
    inference(resolution,[],[f193,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f193,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f192])).

fof(f218,plain,
    ( spl3_20
    | ~ spl3_26
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f212,f192,f216,f184])).

fof(f184,plain,
    ( spl3_20
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f212,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl3_22 ),
    inference(resolution,[],[f193,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f211,plain,
    ( ~ spl3_4
    | ~ spl3_17
    | spl3_1
    | spl3_23
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f198,f163,f200,f77,f167,f91])).

fof(f167,plain,
    ( spl3_17
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f77,plain,
    ( spl3_1
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f200,plain,
    ( spl3_23
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f163,plain,
    ( spl3_16
  <=> u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f198,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_16 ),
    inference(superposition,[],[f60,f164])).

fof(f164,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f60,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f194,plain,
    ( spl3_21
    | spl3_22
    | ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f187,f80,f87,f192,f189])).

fof(f187,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl3_2 ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f81,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f186,plain,
    ( spl3_5
    | ~ spl3_20
    | ~ spl3_4
    | ~ spl3_17
    | spl3_13
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f182,f77,f146,f167,f91,f184,f95])).

fof(f146,plain,
    ( spl3_13
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f182,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f83,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f83,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f177,plain,
    ( ~ spl3_4
    | ~ spl3_17
    | spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f175,f160,f77,f167,f91])).

fof(f160,plain,
    ( spl3_15
  <=> v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f175,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_15 ),
    inference(resolution,[],[f161,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f161,plain,
    ( v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f160])).

fof(f174,plain,
    ( spl3_5
    | ~ spl3_4
    | ~ spl3_3
    | spl3_17 ),
    inference(avatar_split_clause,[],[f173,f167,f87,f91,f95])).

fof(f173,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_17 ),
    inference(resolution,[],[f168,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f168,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f165,plain,
    ( spl3_15
    | spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f157,f154,f163,f160])).

fof(f154,plain,
    ( spl3_14
  <=> m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f157,plain,
    ( u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl3_14 ),
    inference(resolution,[],[f155,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f155,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f156,plain,
    ( spl3_5
    | spl3_14
    | ~ spl3_4
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f152,f87,f77,f91,f154,f95])).

fof(f152,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f102,f88])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_tex_2(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f59,f71])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f151,plain,
    ( spl3_5
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f150,f146,f87,f91,f95])).

fof(f150,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_13 ),
    inference(resolution,[],[f147,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f147,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f118,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f116,f107,f91,f87,f95])).

fof(f107,plain,
    ( spl3_6
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f108,f71])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f114,plain,
    ( spl3_6
    | ~ spl3_4
    | spl3_7
    | spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f105,f87,f95,f111,f91,f107])).

fof(f111,plain,
    ( spl3_7
  <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f105,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f104,f88])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f103,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (30171)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0,X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f98,f56])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(k1_tex_2(X1,X0))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0))) ) ),
    inference(resolution,[],[f73,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f73,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f97,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f50,f95])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f93,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f51,f91])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f87])).

fof(f52,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f53,f80,f77])).

fof(f53,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f54,f80,f77])).

fof(f54,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:09:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (30169)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (30161)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (30161)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f82,f85,f89,f93,f97,f114,f118,f151,f156,f165,f174,f177,f186,f194,f211,f218,f222,f225,f227,f277,f278])).
% 0.20/0.49  fof(f278,plain,(
% 0.20/0.49    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    ~spl3_2 | ~spl3_3 | ~spl3_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f276,f220,f87,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl3_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl3_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    spl3_27 <=> ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl3_3 | ~spl3_27)),
% 0.20/0.49    inference(resolution,[],[f221,f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f87])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))) ) | ~spl3_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f220])).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    spl3_5 | ~spl3_26 | ~spl3_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f226,f189,f216,f95])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    spl3_5 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    spl3_26 <=> l1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    spl3_21 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_21),
% 0.20/0.49    inference(resolution,[],[f190,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f189])).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    ~spl3_4 | spl3_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f224,f216,f91])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl3_4 <=> l1_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | spl3_26),
% 0.20/0.49    inference(resolution,[],[f217,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    ~l1_struct_0(sK0) | spl3_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f216])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    spl3_21 | spl3_27 | ~spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f213,f192,f220,f189])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    spl3_22 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl3_22),
% 0.20/0.49    inference(resolution,[],[f193,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | ~spl3_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f192])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    spl3_20 | ~spl3_26 | ~spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f212,f192,f216,f184])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    spl3_20 <=> v7_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    ~l1_struct_0(sK0) | v7_struct_0(sK0) | ~spl3_22),
% 0.20/0.49    inference(resolution,[],[f193,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    ~spl3_4 | ~spl3_17 | spl3_1 | spl3_23 | ~spl3_16),
% 0.20/0.49    inference(avatar_split_clause,[],[f198,f163,f200,f77,f167,f91])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    spl3_17 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl3_1 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    spl3_23 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    spl3_16 <=> u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl3_16),
% 0.20/0.49    inference(superposition,[],[f60,f164])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~spl3_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f163])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(rectify,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    spl3_21 | spl3_22 | ~spl3_3 | spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f187,f80,f87,f192,f189])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl3_2),
% 0.20/0.49    inference(resolution,[],[f81,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f80])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    spl3_5 | ~spl3_20 | ~spl3_4 | ~spl3_17 | spl3_13 | ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f182,f77,f146,f167,f91,f184,f95])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    spl3_13 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v7_struct_0(sK0) | v2_struct_0(sK0) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f83,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f77])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    ~spl3_4 | ~spl3_17 | spl3_1 | ~spl3_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f175,f160,f77,f167,f91])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    spl3_15 <=> v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl3_15),
% 0.20/0.49    inference(resolution,[],[f161,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f160])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    spl3_5 | ~spl3_4 | ~spl3_3 | spl3_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f173,f167,f87,f91,f95])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_17),
% 0.20/0.49    inference(resolution,[],[f168,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f167])).
% 0.20/0.49  fof(f165,plain,(
% 0.20/0.49    spl3_15 | spl3_16 | ~spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f157,f154,f163,f160])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    spl3_14 <=> m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    u1_struct_0(sK0) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl3_14),
% 0.20/0.49    inference(resolution,[],[f155,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f154])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    spl3_5 | spl3_14 | ~spl3_4 | spl3_1 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f152,f87,f77,f91,f154,f95])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl3_3),
% 0.20/0.49    inference(resolution,[],[f102,f88])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | m1_subset_1(sK2(X0,k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f101])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(sK2(X0,k1_tex_2(X0,X1)),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f59,f71])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    spl3_5 | ~spl3_4 | ~spl3_3 | ~spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f150,f146,f87,f91,f95])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_13),
% 0.20/0.49    inference(resolution,[],[f147,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f146])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    spl3_5 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f116,f107,f91,f87,f95])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl3_6 <=> ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl3_6),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f115])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_6),
% 0.20/0.49    inference(resolution,[],[f108,f71])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f107])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl3_6 | ~spl3_4 | spl3_7 | spl3_5 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f105,f87,f95,f111,f91,f107])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl3_7 <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK0) | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_3),
% 0.20/0.49    inference(resolution,[],[f104,f88])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0,X1))) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_tex_2(X0,X1),X2) | ~l1_pre_topc(X2)) )),
% 0.20/0.49    inference(resolution,[],[f103,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  % (30171)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0,X1))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(resolution,[],[f98,f56])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_struct_0(k1_tex_2(X1,X0)) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1,X0)))) )),
% 0.20/0.49    inference(resolution,[],[f73,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ~spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f50,f95])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f51,f91])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f52,f87])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl3_1 | spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f53,f80,f77])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f54,f80,f77])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f44])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (30161)------------------------------
% 0.20/0.49  % (30161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (30161)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (30161)Memory used [KB]: 10746
% 0.20/0.49  % (30164)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (30161)Time elapsed: 0.014 s
% 0.20/0.49  % (30161)------------------------------
% 0.20/0.49  % (30161)------------------------------
% 0.20/0.49  % (30154)Success in time 0.13 s
%------------------------------------------------------------------------------
