%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:25 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 394 expanded)
%              Number of leaves         :   18 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          :  316 (2413 expanded)
%              Number of equality atoms :   62 ( 570 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f47,f77,f94,f117,f120,f123,f132,f145,f146,f148,f151,f153,f155])).

fof(f155,plain,(
    ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f24,f106])).

fof(f106,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) )
            & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | ~ v3_pre_topc(X1,sK0) )
          & ( k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ( k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | ~ v3_pre_topc(X1,sK0) )
        & ( k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
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
           => ( v3_pre_topc(X1,X0)
            <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f153,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f152,f39,f57])).

fof(f57,plain,
    ( spl2_4
  <=> r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f39,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f152,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(global_subsumption,[],[f26,f135])).

fof(f135,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f151,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f150,f57,f54])).

fof(f54,plain,
    ( spl2_3
  <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f150,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(global_subsumption,[],[f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(global_subsumption,[],[f24,f25,f26,f48])).

fof(f48,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f148,plain,
    ( spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f147,f57,f39])).

fof(f147,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f26,f136])).

fof(f136,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f27,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f146,plain,
    ( ~ spl2_5
    | spl2_7
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f142,f54,f75,f68])).

fof(f68,plain,
    ( spl2_5
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f75,plain,
    ( spl2_7
  <=> ! [X7,X6] :
        ( k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7)
        | u1_pre_topc(sK0) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f142,plain,
    ( ! [X4,X5] :
        ( k6_tmap_1(sK0,sK1) != g1_pre_topc(X4,X5)
        | u1_pre_topc(sK0) = X5
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_3 ),
    inference(superposition,[],[f37,f130])).

fof(f130,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f60,f55])).

fof(f55,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f60,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f24,f25,f26,f49])).

fof(f49,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f145,plain,
    ( spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f43,f130])).

fof(f43,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_2
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f132,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl2_13 ),
    inference(subsumption_resolution,[],[f27,f115])).

fof(f115,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl2_13
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f123,plain,(
    spl2_12 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl2_12 ),
    inference(subsumption_resolution,[],[f26,f112])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f120,plain,(
    spl2_11 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl2_11 ),
    inference(subsumption_resolution,[],[f25,f109])).

fof(f109,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f117,plain,
    ( spl2_10
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f103,f75,f57,f114,f111,f108,f105])).

fof(f103,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_7 ),
    inference(trivial_inequality_removal,[],[f102])).

fof(f102,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_7 ),
    inference(superposition,[],[f35,f99])).

fof(f99,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_7 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_7 ),
    inference(superposition,[],[f76,f60])).

fof(f76,plain,
    ( ! [X6,X7] :
        ( k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7)
        | u1_pre_topc(sK0) = X7 )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f35,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f26,f78])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(resolution,[],[f69,f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f69,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f77,plain,
    ( ~ spl2_5
    | spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f66,f42,f75,f68])).

fof(f66,plain,
    ( ! [X6,X7] :
        ( k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7)
        | u1_pre_topc(sK0) = X7
        | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_2 ),
    inference(superposition,[],[f37,f46])).

fof(f46,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f47,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f28,f42,f39])).

fof(f28,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f29,f42,f39])).

fof(f29,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:29:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.49/0.57  % (8787)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.49/0.57  % (8799)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.49/0.57  % (8787)Refutation found. Thanks to Tanya!
% 1.49/0.57  % SZS status Theorem for theBenchmark
% 1.49/0.58  % (8801)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.58  % (8790)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.49/0.58  % (8793)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.58  % (8795)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.49/0.58  % (8809)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.59  % (8811)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.49/0.59  % SZS output start Proof for theBenchmark
% 1.49/0.59  fof(f156,plain,(
% 1.49/0.59    $false),
% 1.49/0.59    inference(avatar_sat_refutation,[],[f44,f47,f77,f94,f117,f120,f123,f132,f145,f146,f148,f151,f153,f155])).
% 1.49/0.59  fof(f155,plain,(
% 1.49/0.59    ~spl2_10),
% 1.49/0.59    inference(avatar_contradiction_clause,[],[f154])).
% 1.49/0.59  fof(f154,plain,(
% 1.49/0.59    $false | ~spl2_10),
% 1.49/0.59    inference(subsumption_resolution,[],[f24,f106])).
% 1.49/0.59  fof(f106,plain,(
% 1.49/0.59    v2_struct_0(sK0) | ~spl2_10),
% 1.49/0.59    inference(avatar_component_clause,[],[f105])).
% 1.49/0.59  fof(f105,plain,(
% 1.49/0.59    spl2_10 <=> v2_struct_0(sK0)),
% 1.49/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.49/0.59  fof(f24,plain,(
% 1.49/0.59    ~v2_struct_0(sK0)),
% 1.49/0.59    inference(cnf_transformation,[],[f21])).
% 1.49/0.59  fof(f21,plain,(
% 1.49/0.59    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.49/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20,f19])).
% 1.49/0.59  fof(f19,plain,(
% 1.49/0.59    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X1,sK0)) & (k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.49/0.59    introduced(choice_axiom,[])).
% 1.74/0.59  fof(f20,plain,(
% 1.74/0.59    ? [X1] : ((k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X1,sK0)) & (k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.74/0.59    introduced(choice_axiom,[])).
% 1.74/0.59  fof(f18,plain,(
% 1.74/0.59    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.74/0.59    inference(flattening,[],[f17])).
% 1.74/0.59  fof(f17,plain,(
% 1.74/0.59    ? [X0] : (? [X1] : (((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.74/0.59    inference(nnf_transformation,[],[f9])).
% 1.74/0.59  fof(f9,plain,(
% 1.74/0.59    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.74/0.59    inference(flattening,[],[f8])).
% 1.74/0.59  fof(f8,plain,(
% 1.74/0.59    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.74/0.59    inference(ennf_transformation,[],[f7])).
% 1.74/0.59  fof(f7,negated_conjecture,(
% 1.74/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.74/0.59    inference(negated_conjecture,[],[f6])).
% 1.74/0.59  fof(f6,conjecture,(
% 1.74/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).
% 1.74/0.59  fof(f153,plain,(
% 1.74/0.59    spl2_4 | ~spl2_1),
% 1.74/0.59    inference(avatar_split_clause,[],[f152,f39,f57])).
% 1.74/0.59  fof(f57,plain,(
% 1.74/0.59    spl2_4 <=> r2_hidden(sK1,u1_pre_topc(sK0))),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.74/0.59  fof(f39,plain,(
% 1.74/0.59    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.74/0.59  fof(f152,plain,(
% 1.74/0.59    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 1.74/0.59    inference(global_subsumption,[],[f26,f135])).
% 1.74/0.59  fof(f135,plain,(
% 1.74/0.59    ~v3_pre_topc(sK1,sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 1.74/0.59    inference(resolution,[],[f27,f31])).
% 1.74/0.59  fof(f31,plain,(
% 1.74/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f22])).
% 1.74/0.59  fof(f22,plain,(
% 1.74/0.59    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.74/0.59    inference(nnf_transformation,[],[f11])).
% 1.74/0.59  fof(f11,plain,(
% 1.74/0.59    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.74/0.59    inference(ennf_transformation,[],[f1])).
% 1.74/0.59  fof(f1,axiom,(
% 1.74/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.74/0.59  fof(f27,plain,(
% 1.74/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.59    inference(cnf_transformation,[],[f21])).
% 1.74/0.59  fof(f26,plain,(
% 1.74/0.59    l1_pre_topc(sK0)),
% 1.74/0.59    inference(cnf_transformation,[],[f21])).
% 1.74/0.59  fof(f151,plain,(
% 1.74/0.59    spl2_3 | ~spl2_4),
% 1.74/0.59    inference(avatar_split_clause,[],[f150,f57,f54])).
% 1.74/0.59  fof(f54,plain,(
% 1.74/0.59    spl2_3 <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.74/0.59  fof(f150,plain,(
% 1.74/0.59    ~r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 1.74/0.59    inference(global_subsumption,[],[f52])).
% 1.74/0.59  fof(f52,plain,(
% 1.74/0.59    ~r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 1.74/0.59    inference(global_subsumption,[],[f24,f25,f26,f48])).
% 1.74/0.59  fof(f48,plain,(
% 1.74/0.59    ~r2_hidden(sK1,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.59    inference(resolution,[],[f27,f34])).
% 1.74/0.59  fof(f34,plain,(
% 1.74/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f23])).
% 1.74/0.59  fof(f23,plain,(
% 1.74/0.59    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.59    inference(nnf_transformation,[],[f15])).
% 1.74/0.59  fof(f15,plain,(
% 1.74/0.59    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.59    inference(flattening,[],[f14])).
% 1.74/0.59  fof(f14,plain,(
% 1.74/0.59    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.59    inference(ennf_transformation,[],[f5])).
% 1.74/0.59  fof(f5,axiom,(
% 1.74/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 1.74/0.59  fof(f25,plain,(
% 1.74/0.59    v2_pre_topc(sK0)),
% 1.74/0.59    inference(cnf_transformation,[],[f21])).
% 1.74/0.59  fof(f148,plain,(
% 1.74/0.59    spl2_1 | ~spl2_4),
% 1.74/0.59    inference(avatar_split_clause,[],[f147,f57,f39])).
% 1.74/0.59  fof(f147,plain,(
% 1.74/0.59    ~r2_hidden(sK1,u1_pre_topc(sK0)) | v3_pre_topc(sK1,sK0)),
% 1.74/0.59    inference(global_subsumption,[],[f26,f136])).
% 1.74/0.59  fof(f136,plain,(
% 1.74/0.59    ~r2_hidden(sK1,u1_pre_topc(sK0)) | v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.74/0.59    inference(resolution,[],[f27,f32])).
% 1.74/0.59  fof(f32,plain,(
% 1.74/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f22])).
% 1.74/0.59  fof(f146,plain,(
% 1.74/0.59    ~spl2_5 | spl2_7 | ~spl2_3),
% 1.74/0.59    inference(avatar_split_clause,[],[f142,f54,f75,f68])).
% 1.74/0.59  fof(f68,plain,(
% 1.74/0.59    spl2_5 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.74/0.59  fof(f75,plain,(
% 1.74/0.59    spl2_7 <=> ! [X7,X6] : (k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7) | u1_pre_topc(sK0) = X7)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.74/0.59  fof(f142,plain,(
% 1.74/0.59    ( ! [X4,X5] : (k6_tmap_1(sK0,sK1) != g1_pre_topc(X4,X5) | u1_pre_topc(sK0) = X5 | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl2_3),
% 1.74/0.59    inference(superposition,[],[f37,f130])).
% 1.74/0.59  fof(f130,plain,(
% 1.74/0.59    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~spl2_3),
% 1.74/0.59    inference(forward_demodulation,[],[f60,f55])).
% 1.74/0.59  fof(f55,plain,(
% 1.74/0.59    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~spl2_3),
% 1.74/0.59    inference(avatar_component_clause,[],[f54])).
% 1.74/0.59  fof(f60,plain,(
% 1.74/0.59    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 1.74/0.59    inference(global_subsumption,[],[f24,f25,f26,f49])).
% 1.74/0.59  fof(f49,plain,(
% 1.74/0.59    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.74/0.59    inference(resolution,[],[f27,f33])).
% 1.74/0.59  fof(f33,plain,(
% 1.74/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f13])).
% 1.74/0.59  fof(f13,plain,(
% 1.74/0.59    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.59    inference(flattening,[],[f12])).
% 1.74/0.59  fof(f12,plain,(
% 1.74/0.59    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.59    inference(ennf_transformation,[],[f4])).
% 1.74/0.59  fof(f4,axiom,(
% 1.74/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).
% 1.74/0.59  fof(f37,plain,(
% 1.74/0.59    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.74/0.59    inference(cnf_transformation,[],[f16])).
% 1.74/0.59  fof(f16,plain,(
% 1.74/0.59    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.74/0.59    inference(ennf_transformation,[],[f3])).
% 1.74/0.59  fof(f3,axiom,(
% 1.74/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.74/0.59  fof(f145,plain,(
% 1.74/0.59    spl2_2 | ~spl2_3),
% 1.74/0.59    inference(avatar_contradiction_clause,[],[f139])).
% 1.74/0.59  fof(f139,plain,(
% 1.74/0.59    $false | (spl2_2 | ~spl2_3)),
% 1.74/0.59    inference(subsumption_resolution,[],[f43,f130])).
% 1.74/0.59  fof(f43,plain,(
% 1.74/0.59    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | spl2_2),
% 1.74/0.59    inference(avatar_component_clause,[],[f42])).
% 1.74/0.59  fof(f42,plain,(
% 1.74/0.59    spl2_2 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.74/0.59  fof(f132,plain,(
% 1.74/0.59    spl2_13),
% 1.74/0.59    inference(avatar_contradiction_clause,[],[f131])).
% 1.74/0.59  fof(f131,plain,(
% 1.74/0.59    $false | spl2_13),
% 1.74/0.59    inference(subsumption_resolution,[],[f27,f115])).
% 1.74/0.59  fof(f115,plain,(
% 1.74/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_13),
% 1.74/0.59    inference(avatar_component_clause,[],[f114])).
% 1.74/0.59  fof(f114,plain,(
% 1.74/0.59    spl2_13 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.74/0.59  fof(f123,plain,(
% 1.74/0.59    spl2_12),
% 1.74/0.59    inference(avatar_contradiction_clause,[],[f122])).
% 1.74/0.59  fof(f122,plain,(
% 1.74/0.59    $false | spl2_12),
% 1.74/0.59    inference(subsumption_resolution,[],[f26,f112])).
% 1.74/0.59  fof(f112,plain,(
% 1.74/0.59    ~l1_pre_topc(sK0) | spl2_12),
% 1.74/0.59    inference(avatar_component_clause,[],[f111])).
% 1.74/0.59  fof(f111,plain,(
% 1.74/0.59    spl2_12 <=> l1_pre_topc(sK0)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.74/0.59  fof(f120,plain,(
% 1.74/0.59    spl2_11),
% 1.74/0.59    inference(avatar_contradiction_clause,[],[f119])).
% 1.74/0.59  fof(f119,plain,(
% 1.74/0.59    $false | spl2_11),
% 1.74/0.59    inference(subsumption_resolution,[],[f25,f109])).
% 1.74/0.59  fof(f109,plain,(
% 1.74/0.59    ~v2_pre_topc(sK0) | spl2_11),
% 1.74/0.59    inference(avatar_component_clause,[],[f108])).
% 1.74/0.59  fof(f108,plain,(
% 1.74/0.59    spl2_11 <=> v2_pre_topc(sK0)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.74/0.59  fof(f117,plain,(
% 1.74/0.59    spl2_10 | ~spl2_11 | ~spl2_12 | ~spl2_13 | spl2_4 | ~spl2_7),
% 1.74/0.59    inference(avatar_split_clause,[],[f103,f75,f57,f114,f111,f108,f105])).
% 1.74/0.59  fof(f103,plain,(
% 1.74/0.59    r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_7),
% 1.74/0.59    inference(trivial_inequality_removal,[],[f102])).
% 1.74/0.59  fof(f102,plain,(
% 1.74/0.59    u1_pre_topc(sK0) != u1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_7),
% 1.74/0.59    inference(superposition,[],[f35,f99])).
% 1.74/0.59  fof(f99,plain,(
% 1.74/0.59    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~spl2_7),
% 1.74/0.59    inference(trivial_inequality_removal,[],[f98])).
% 1.74/0.59  fof(f98,plain,(
% 1.74/0.59    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~spl2_7),
% 1.74/0.59    inference(superposition,[],[f76,f60])).
% 1.74/0.59  fof(f76,plain,(
% 1.74/0.59    ( ! [X6,X7] : (k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7) | u1_pre_topc(sK0) = X7) ) | ~spl2_7),
% 1.74/0.59    inference(avatar_component_clause,[],[f75])).
% 1.74/0.59  fof(f35,plain,(
% 1.74/0.59    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f23])).
% 1.74/0.59  fof(f94,plain,(
% 1.74/0.59    spl2_5),
% 1.74/0.59    inference(avatar_contradiction_clause,[],[f93])).
% 1.74/0.59  fof(f93,plain,(
% 1.74/0.59    $false | spl2_5),
% 1.74/0.59    inference(subsumption_resolution,[],[f26,f78])).
% 1.74/0.59  fof(f78,plain,(
% 1.74/0.59    ~l1_pre_topc(sK0) | spl2_5),
% 1.74/0.59    inference(resolution,[],[f69,f30])).
% 1.74/0.59  fof(f30,plain,(
% 1.74/0.59    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f10])).
% 1.74/0.59  fof(f10,plain,(
% 1.74/0.59    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.74/0.59    inference(ennf_transformation,[],[f2])).
% 1.74/0.59  fof(f2,axiom,(
% 1.74/0.59    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.74/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.74/0.59  fof(f69,plain,(
% 1.74/0.59    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_5),
% 1.74/0.59    inference(avatar_component_clause,[],[f68])).
% 1.74/0.59  fof(f77,plain,(
% 1.74/0.59    ~spl2_5 | spl2_7 | ~spl2_2),
% 1.74/0.59    inference(avatar_split_clause,[],[f66,f42,f75,f68])).
% 1.74/0.59  fof(f66,plain,(
% 1.74/0.59    ( ! [X6,X7] : (k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7) | u1_pre_topc(sK0) = X7 | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl2_2),
% 1.74/0.59    inference(superposition,[],[f37,f46])).
% 1.74/0.59  fof(f46,plain,(
% 1.74/0.59    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~spl2_2),
% 1.74/0.59    inference(avatar_component_clause,[],[f42])).
% 1.74/0.59  fof(f47,plain,(
% 1.74/0.59    spl2_1 | spl2_2),
% 1.74/0.59    inference(avatar_split_clause,[],[f28,f42,f39])).
% 1.74/0.59  fof(f28,plain,(
% 1.74/0.59    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 1.74/0.59    inference(cnf_transformation,[],[f21])).
% 1.74/0.59  fof(f44,plain,(
% 1.74/0.59    ~spl2_1 | ~spl2_2),
% 1.74/0.59    inference(avatar_split_clause,[],[f29,f42,f39])).
% 1.74/0.59  fof(f29,plain,(
% 1.74/0.59    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.74/0.59    inference(cnf_transformation,[],[f21])).
% 1.74/0.59  % SZS output end Proof for theBenchmark
% 1.74/0.59  % (8787)------------------------------
% 1.74/0.59  % (8787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.59  % (8787)Termination reason: Refutation
% 1.74/0.59  
% 1.74/0.59  % (8787)Memory used [KB]: 10746
% 1.74/0.59  % (8787)Time elapsed: 0.132 s
% 1.74/0.59  % (8787)------------------------------
% 1.74/0.59  % (8787)------------------------------
% 1.74/0.60  % (8784)Success in time 0.226 s
%------------------------------------------------------------------------------
