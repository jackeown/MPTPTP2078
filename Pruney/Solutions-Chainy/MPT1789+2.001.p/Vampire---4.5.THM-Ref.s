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
% DateTime   : Thu Dec  3 13:19:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 148 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  252 ( 538 expanded)
%              Number of equality atoms :   63 ( 155 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f64,f69,f74,f81,f87,f125,f132])).

fof(f132,plain,
    ( spl2_1
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f131,f85,f79,f72,f34])).

fof(f34,plain,
    ( spl2_1
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f72,plain,
    ( spl2_9
  <=> m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f79,plain,
    ( spl2_10
  <=> g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f85,plain,
    ( spl2_11
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f131,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f117,f86])).

fof(f86,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f117,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)))
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)))
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(superposition,[],[f77,f80])).

fof(f80,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f77,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
        | u1_struct_0(sK0) = X2 )
    | ~ spl2_9 ),
    inference(resolution,[],[f73,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f73,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f125,plain,
    ( spl2_2
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f124,f85,f79,f72,f37])).

fof(f37,plain,
    ( spl2_2
  <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f124,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f118,f86])).

fof(f118,plain,
    ( k5_tmap_1(sK0,sK1) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)))
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)))
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(superposition,[],[f76,f80])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
        | k5_tmap_1(sK0,sK1) = X1 )
    | ~ spl2_9 ),
    inference(resolution,[],[f73,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f83,f67,f41,f85])).

fof(f41,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( spl2_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f83,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f81,plain,
    ( spl2_10
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f75,f72,f79])).

fof(f75,plain,
    ( g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))))
    | ~ spl2_9 ),
    inference(resolution,[],[f73,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) ) ),
    inference(global_subsumption,[],[f29,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
      | ~ l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f26,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f29,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f70,f62,f41,f72])).

fof(f62,plain,
    ( spl2_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f70,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f63,f42])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f69,plain,
    ( spl2_6
    | ~ spl2_4
    | spl2_8
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f65,f49,f67,f45,f53])).

fof(f53,plain,
    ( spl2_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f45,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f49,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f65,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_5 ),
    inference(resolution,[],[f27,f50])).

fof(f50,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f64,plain,
    ( spl2_6
    | ~ spl2_4
    | spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f58,f49,f62,f45,f53])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl2_5 ),
    inference(resolution,[],[f32,f50])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).

fof(f55,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
      | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
              | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1))
            | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ( k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1))
          | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
        | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1))
            | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
              & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f51,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f25,f37,f34])).

fof(f25,plain,
    ( k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1))
    | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:39:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (1340)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (1340)Refutation not found, incomplete strategy% (1340)------------------------------
% 0.21/0.51  % (1340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1338)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (1357)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (1341)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (1340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1340)Memory used [KB]: 10746
% 0.21/0.52  % (1340)Time elapsed: 0.098 s
% 0.21/0.52  % (1340)------------------------------
% 0.21/0.52  % (1340)------------------------------
% 0.21/0.52  % (1339)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (1344)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (1353)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (1357)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f39,f43,f47,f51,f55,f64,f69,f74,f81,f87,f125,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl2_1 | ~spl2_9 | ~spl2_10 | ~spl2_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f131,f85,f79,f72,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    spl2_1 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl2_9 <=> m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl2_10 <=> g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl2_11 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | (~spl2_9 | ~spl2_10 | ~spl2_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f117,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | ~spl2_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))) | (~spl2_9 | ~spl2_10)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))) | (~spl2_9 | ~spl2_10)),
% 0.21/0.52    inference(superposition,[],[f77,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)))) | ~spl2_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f79])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X2,X3] : (g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | u1_struct_0(sK0) = X2) ) | ~spl2_9),
% 0.21/0.52    inference(resolution,[],[f73,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl2_2 | ~spl2_9 | ~spl2_10 | ~spl2_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f124,f85,f79,f72,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    spl2_2 <=> k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl2_9 | ~spl2_10 | ~spl2_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f118,f86])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    k5_tmap_1(sK0,sK1) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))) | (~spl2_9 | ~spl2_10)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | k5_tmap_1(sK0,sK1) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))) | (~spl2_9 | ~spl2_10)),
% 0.21/0.52    inference(superposition,[],[f76,f80])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | k5_tmap_1(sK0,sK1) = X1) ) | ~spl2_9),
% 0.21/0.52    inference(resolution,[],[f73,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl2_11 | ~spl2_3 | ~spl2_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f83,f67,f41,f85])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl2_8 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | (~spl2_3 | ~spl2_8)),
% 0.21/0.52    inference(resolution,[],[f68,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f41])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))) ) | ~spl2_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f67])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl2_10 | ~spl2_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f75,f72,f79])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)))) | ~spl2_9),
% 0.21/0.52    inference(resolution,[],[f73,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))) )),
% 0.21/0.52    inference(global_subsumption,[],[f29,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) | ~l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(resolution,[],[f26,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl2_9 | ~spl2_3 | ~spl2_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f70,f62,f41,f72])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl2_7 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl2_3 | ~spl2_7)),
% 0.21/0.52    inference(resolution,[],[f63,f42])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f62])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl2_6 | ~spl2_4 | spl2_8 | ~spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f65,f49,f67,f45,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl2_6 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl2_4 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl2_5 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl2_5),
% 0.21/0.52    inference(resolution,[],[f27,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f49])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl2_6 | ~spl2_4 | spl2_7 | ~spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f58,f49,f62,f45,f53])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_struct_0(sK0)) ) | ~spl2_5),
% 0.21/0.52    inference(resolution,[],[f32,f50])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ~spl2_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f53])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ((k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1)) | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X1] : ((k5_tmap_1(sK0,X1) != u1_pre_topc(k6_tmap_1(sK0,X1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1)) | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((k5_tmap_1(X0,X1) != u1_pre_topc(k6_tmap_1(X0,X1)) | u1_struct_0(X0) != u1_struct_0(k6_tmap_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f45])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f41])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ~spl2_1 | ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f37,f34])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k5_tmap_1(sK0,sK1) != u1_pre_topc(k6_tmap_1(sK0,sK1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (1357)------------------------------
% 0.21/0.52  % (1357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1357)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (1357)Memory used [KB]: 10746
% 0.21/0.52  % (1357)Time elapsed: 0.116 s
% 0.21/0.52  % (1357)------------------------------
% 0.21/0.52  % (1357)------------------------------
% 0.21/0.52  % (1337)Success in time 0.158 s
%------------------------------------------------------------------------------
