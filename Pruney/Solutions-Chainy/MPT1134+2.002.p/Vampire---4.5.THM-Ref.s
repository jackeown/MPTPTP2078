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
% DateTime   : Thu Dec  3 13:09:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 128 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :  228 ( 458 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f42,f47,f52,f64,f76,f102,f120,f155,f185])).

fof(f185,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4
    | spl3_16 ),
    inference(trivial_inequality_removal,[],[f182])).

fof(f182,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl3_1
    | ~ spl3_4
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f51,f35,f154,f31])).

fof(f31,plain,(
    ! [X2,X0,X3] :
      ( sP2(X3,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f31_D])).

fof(f31_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
          | ~ l1_pre_topc(X2)
          | ~ m1_pre_topc(X2,X0) )
    <=> ~ sP2(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).

fof(f154,plain,
    ( ~ sP2(sK0,sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_16
  <=> sP2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f35,plain,
    ( m1_pre_topc(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> m1_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f51,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f155,plain,
    ( ~ spl3_16
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f145,f116,f99,f49,f44,f38,f152])).

fof(f38,plain,
    ( spl3_2
  <=> m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f44,plain,
    ( spl3_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f99,plain,
    ( spl3_10
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f116,plain,
    ( spl3_12
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f145,plain,
    ( ~ sP2(sK0,sK1)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f51,f46,f101,f40,f118,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | m1_pre_topc(X3,X1)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ sP2(X3,X0) ) ),
    inference(general_splitting,[],[f28,f31_D])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

fof(f118,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f40,plain,
    ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f101,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f46,plain,
    ( l1_pre_topc(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f120,plain,
    ( spl3_12
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f114,f61,f116])).

fof(f61,plain,
    ( spl3_6
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f114,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl3_6 ),
    inference(resolution,[],[f66,f63])).

fof(f63,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) ) ),
    inference(global_subsumption,[],[f26,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
      | ~ l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f29,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f26,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f91,f61,f99])).

fof(f91,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f63,f26])).

fof(f76,plain,
    ( ~ spl3_3
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f71,f38,f34,f44])).

fof(f71,plain,
    ( m1_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f64,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f53,f44,f61])).

fof(f53,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f46,f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_pre_topc(sK0,sK1) )
    & ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | m1_pre_topc(sK0,sK1) )
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | m1_pre_topc(X0,X1) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ m1_pre_topc(sK0,X1) )
          & ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | m1_pre_topc(sK0,X1) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | ~ m1_pre_topc(sK0,X1) )
        & ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
          | m1_pre_topc(sK0,X1) )
        & l1_pre_topc(X1) )
   => ( ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_pre_topc(sK0,sK1) )
      & ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | m1_pre_topc(sK0,sK1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ m1_pre_topc(X0,X1) )
          & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | m1_pre_topc(X0,X1) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | ~ m1_pre_topc(X0,X1) )
          & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            | m1_pre_topc(X0,X1) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_pre_topc(X0,X1)
          <~> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( m1_pre_topc(X0,X1)
            <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f23,f38,f34])).

fof(f23,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | m1_pre_topc(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f38,f34])).

fof(f24,plain,
    ( ~ m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_pre_topc(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:19:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.44  % (981)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.45  % (981)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f186,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f41,f42,f47,f52,f64,f76,f102,f120,f155,f185])).
% 0.19/0.45  fof(f185,plain,(
% 0.19/0.45    ~spl3_1 | ~spl3_4 | spl3_16),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f184])).
% 0.19/0.45  fof(f184,plain,(
% 0.19/0.45    $false | (~spl3_1 | ~spl3_4 | spl3_16)),
% 0.19/0.45    inference(trivial_inequality_removal,[],[f182])).
% 0.19/0.45  fof(f182,plain,(
% 0.19/0.45    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | (~spl3_1 | ~spl3_4 | spl3_16)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f51,f35,f154,f31])).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    ( ! [X2,X0,X3] : (sP2(X3,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f31_D])).
% 0.19/0.45  fof(f31_D,plain,(
% 0.19/0.45    ( ! [X0,X3] : (( ! [X2] : (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | ~l1_pre_topc(X2) | ~m1_pre_topc(X2,X0)) ) <=> ~sP2(X3,X0)) )),
% 0.19/0.45    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
% 0.19/0.45  fof(f154,plain,(
% 0.19/0.45    ~sP2(sK0,sK1) | spl3_16),
% 0.19/0.45    inference(avatar_component_clause,[],[f152])).
% 0.19/0.45  fof(f152,plain,(
% 0.19/0.45    spl3_16 <=> sP2(sK0,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    m1_pre_topc(sK0,sK1) | ~spl3_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f34])).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    spl3_1 <=> m1_pre_topc(sK0,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    l1_pre_topc(sK0) | ~spl3_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f49])).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    spl3_4 <=> l1_pre_topc(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.45  fof(f155,plain,(
% 0.19/0.45    ~spl3_16 | spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_12),
% 0.19/0.45    inference(avatar_split_clause,[],[f145,f116,f99,f49,f44,f38,f152])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    spl3_2 <=> m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    spl3_3 <=> l1_pre_topc(sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.45  fof(f99,plain,(
% 0.19/0.45    spl3_10 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.45  fof(f116,plain,(
% 0.19/0.45    spl3_12 <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.45  fof(f145,plain,(
% 0.19/0.45    ~sP2(sK0,sK1) | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_12)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f51,f46,f101,f40,f118,f32])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    ( ! [X0,X3,X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | m1_pre_topc(X3,X1) | ~l1_pre_topc(X3) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~sP2(X3,X0)) )),
% 0.19/0.45    inference(general_splitting,[],[f28,f31_D])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(X3,X1) | ~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(flattening,[],[f11])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(X3,X1) | (~m1_pre_topc(X2,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X3)) | ~l1_pre_topc(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (l1_pre_topc(X2) => ! [X3] : (l1_pre_topc(X3) => ((m1_pre_topc(X2,X0) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => m1_pre_topc(X3,X1))))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).
% 0.19/0.45  fof(f118,plain,(
% 0.19/0.45    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl3_12),
% 0.19/0.45    inference(avatar_component_clause,[],[f116])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    ~m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl3_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f38])).
% 0.19/0.45  fof(f101,plain,(
% 0.19/0.45    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl3_10),
% 0.19/0.45    inference(avatar_component_clause,[],[f99])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    l1_pre_topc(sK1) | ~spl3_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f44])).
% 0.19/0.45  fof(f120,plain,(
% 0.19/0.45    spl3_12 | ~spl3_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f114,f61,f116])).
% 0.19/0.45  fof(f61,plain,(
% 0.19/0.45    spl3_6 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.45  fof(f114,plain,(
% 0.19/0.45    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl3_6),
% 0.19/0.45    inference(resolution,[],[f66,f63])).
% 0.19/0.45  fof(f63,plain,(
% 0.19/0.45    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl3_6),
% 0.19/0.45    inference(avatar_component_clause,[],[f61])).
% 0.19/0.45  fof(f66,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))) )),
% 0.19/0.45    inference(global_subsumption,[],[f26,f65])).
% 0.19/0.45  fof(f65,plain,(
% 0.19/0.45    ( ! [X0,X1] : (g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) | ~l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.45    inference(resolution,[],[f29,f25])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(flattening,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f102,plain,(
% 0.19/0.45    spl3_10 | ~spl3_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f91,f61,f99])).
% 0.19/0.45  fof(f91,plain,(
% 0.19/0.45    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl3_6),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f63,f26])).
% 0.19/0.45  fof(f76,plain,(
% 0.19/0.45    ~spl3_3 | spl3_1 | ~spl3_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f71,f38,f34,f44])).
% 0.19/0.45  fof(f71,plain,(
% 0.19/0.45    m1_pre_topc(sK0,sK1) | ~l1_pre_topc(sK1) | ~spl3_2),
% 0.19/0.45    inference(resolution,[],[f27,f39])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl3_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f38])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.19/0.45  fof(f64,plain,(
% 0.19/0.45    spl3_6 | ~spl3_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f53,f44,f61])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl3_3),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f46,f30])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.19/0.45  fof(f52,plain,(
% 0.19/0.45    spl3_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f21,f49])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    l1_pre_topc(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ((~m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(sK0,sK1)) & (m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK0,sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : ((~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : ((~m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(sK0,X1)) & (m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(sK0,X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ? [X1] : ((~m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(sK0,X1)) & (m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(sK0,X1)) & l1_pre_topc(X1)) => ((~m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(sK0,sK1)) & (m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK0,sK1)) & l1_pre_topc(sK1))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : ((~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.19/0.45    inference(flattening,[],[f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (((~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.19/0.45    inference(nnf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : ((m1_pre_topc(X0,X1) <~> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,negated_conjecture,(
% 0.19/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.19/0.45    inference(negated_conjecture,[],[f6])).
% 0.19/0.45  fof(f6,conjecture,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.19/0.45  fof(f47,plain,(
% 0.19/0.45    spl3_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f22,f44])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    l1_pre_topc(sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f42,plain,(
% 0.19/0.45    spl3_1 | spl3_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f23,f38,f34])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | m1_pre_topc(sK0,sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    ~spl3_1 | ~spl3_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f24,f38,f34])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ~m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_pre_topc(sK0,sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (981)------------------------------
% 0.19/0.45  % (981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (981)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (981)Memory used [KB]: 10746
% 0.19/0.45  % (981)Time elapsed: 0.078 s
% 0.19/0.45  % (981)------------------------------
% 0.19/0.45  % (981)------------------------------
% 0.19/0.45  % (968)Success in time 0.116 s
%------------------------------------------------------------------------------
