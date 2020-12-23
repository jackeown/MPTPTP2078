%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:53 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  222 (1282 expanded)
%              Number of leaves         :   33 ( 360 expanded)
%              Depth                    :   24
%              Number of atoms          :  937 (9103 expanded)
%              Number of equality atoms :   66 ( 178 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f931,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f149,f199,f217,f224,f358,f506,f517,f532,f537,f538,f540,f582,f715,f757,f759,f896,f906,f930])).

fof(f930,plain,
    ( ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f929])).

fof(f929,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f928,f908])).

fof(f908,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f147,f904])).

fof(f904,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f194,f903])).

fof(f903,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f902,f88])).

fof(f88,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f69,f71,f70])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f902,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f763,f901])).

fof(f901,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f900,f86])).

fof(f86,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f900,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f892,f88])).

fof(f892,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f891,f89])).

fof(f89,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

fof(f891,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f890,f216])).

fof(f216,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl5_9
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f890,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(resolution,[],[f858,f787])).

fof(f787,plain,
    ( v1_borsuk_1(sK2(sK0,sK1),sK0)
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f786,f85])).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f786,plain,
    ( v1_borsuk_1(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f785,f86])).

fof(f785,plain,
    ( v1_borsuk_1(sK2(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f784,f87])).

fof(f87,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f784,plain,
    ( v1_borsuk_1(sK2(sK0,sK1),sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f781,f88])).

fof(f781,plain,
    ( v1_borsuk_1(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f216,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f858,plain,
    ( ! [X14] :
        ( ~ v1_borsuk_1(sK2(sK0,sK1),X14)
        | ~ m1_pre_topc(sK2(sK0,sK1),X14)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X14)))
        | v4_pre_topc(sK1,X14)
        | ~ l1_pre_topc(X14)
        | ~ v2_pre_topc(X14) )
    | ~ spl5_10 ),
    inference(superposition,[],[f139,f223])).

fof(f223,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl5_10
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f763,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f89,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f194,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl5_5
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f147,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_2
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f928,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(resolution,[],[f907,f138])).

fof(f138,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f907,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f89,f904])).

fof(f906,plain,
    ( ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | spl5_20 ),
    inference(avatar_contradiction_clause,[],[f905])).

fof(f905,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | spl5_20 ),
    inference(subsumption_resolution,[],[f904,f362])).

fof(f362,plain,
    ( u1_struct_0(sK0) != sK1
    | spl5_20 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl5_20
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f896,plain,
    ( spl5_4
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f895])).

fof(f895,plain,
    ( $false
    | spl5_4
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f894,f86])).

fof(f894,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_4
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f893,f88])).

fof(f893,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_4
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f892,f185])).

fof(f185,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl5_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f759,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f758,f183,f179])).

fof(f179,plain,
    ( spl5_3
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f758,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f387,f88])).

fof(f387,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f89,f101])).

fof(f757,plain,
    ( ~ spl5_3
    | spl5_6
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | ~ spl5_3
    | spl5_6
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f755,f560])).

fof(f560,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_20 ),
    inference(backward_demodulation,[],[f89,f363])).

fof(f363,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f361])).

fof(f755,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_3
    | spl5_6
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f754,f363])).

fof(f754,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3
    | spl5_6
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f753,f88])).

fof(f753,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | spl5_6
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f752,f198])).

fof(f198,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl5_6
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f752,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f751,f363])).

fof(f751,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(superposition,[],[f104,f181])).

fof(f181,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f104,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f715,plain,
    ( spl5_6
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | spl5_6
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f198,f713])).

fof(f713,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f712,f560])).

fof(f712,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v1_tops_1(sK1,sK0)
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f711,f363])).

fof(f711,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f705,f88])).

fof(f705,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f704,f363])).

fof(f704,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(superposition,[],[f104,f571])).

fof(f571,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl5_20
    | ~ spl5_23 ),
    inference(backward_demodulation,[],[f550,f363])).

fof(f550,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl5_23 ),
    inference(backward_demodulation,[],[f438,f448])).

fof(f448,plain,
    ( u1_struct_0(sK0) = sK3(sK0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl5_23
  <=> u1_struct_0(sK0) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f438,plain,(
    sK3(sK0) = k2_pre_topc(sK0,sK3(sK0)) ),
    inference(subsumption_resolution,[],[f437,f88])).

fof(f437,plain,
    ( sK3(sK0) = k2_pre_topc(sK0,sK3(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f420,f158])).

fof(f158,plain,(
    v4_pre_topc(sK3(sK0),sK0) ),
    inference(subsumption_resolution,[],[f157,f86])).

fof(f157,plain,
    ( ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK3(sK0),sK0) ),
    inference(subsumption_resolution,[],[f152,f88])).

fof(f152,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK3(sK0),sK0) ),
    inference(resolution,[],[f85,f115])).

fof(f115,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f420,plain,
    ( ~ v4_pre_topc(sK3(sK0),sK0)
    | sK3(sK0) = k2_pre_topc(sK0,sK3(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f154,f101])).

fof(f154,plain,(
    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f153,f86])).

fof(f153,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f150,f88])).

fof(f150,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f85,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f582,plain,
    ( spl5_3
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f581])).

fof(f581,plain,
    ( $false
    | spl5_3
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f563,f180])).

fof(f180,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f179])).

fof(f563,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(backward_demodulation,[],[f194,f363])).

fof(f540,plain,
    ( ~ spl5_19
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f435,f498,f355])).

fof(f355,plain,
    ( spl5_19
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f498,plain,
    ( spl5_30
  <=> v1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f435,plain,
    ( ~ v1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f154,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f538,plain,
    ( spl5_2
    | spl5_20 ),
    inference(avatar_split_clause,[],[f400,f361,f145])).

fof(f400,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f89,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f537,plain,
    ( spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f536,f141,f196])).

fof(f141,plain,
    ( spl5_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f536,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f535,f85])).

fof(f535,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f534,f86])).

fof(f534,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f533,f88])).

fof(f533,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f240])).

fof(f240,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f239,f86])).

fof(f239,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f238,f88])).

fof(f238,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f170,f87])).

fof(f170,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f89,f119])).

fof(f119,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f79,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f167,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f89,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | v1_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f532,plain,
    ( spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f531,f196,f141])).

fof(f531,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f530,f85])).

fof(f530,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f529,f86])).

fof(f529,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f528,f88])).

fof(f528,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f237])).

fof(f237,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f236,f85])).

fof(f236,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f235,f86])).

fof(f235,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f234,f87])).

fof(f234,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f88])).

fof(f169,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f89,f118])).

% (16054)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f166,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f89,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f517,plain,
    ( ~ spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f516,f141,f203])).

fof(f203,plain,
    ( spl5_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f516,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f515,f85])).

fof(f515,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_xboole_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f514,f86])).

fof(f514,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_xboole_0(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f395,f88])).

fof(f395,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f89,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f506,plain,
    ( spl5_30
    | spl5_23 ),
    inference(avatar_split_clause,[],[f433,f446,f498])).

fof(f433,plain,
    ( u1_struct_0(sK0) = sK3(sK0)
    | v1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f154,f128])).

fof(f358,plain,
    ( spl5_19
    | spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f353,f203,f145,f355])).

fof(f353,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f176,f205])).

fof(f205,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f203])).

fof(f176,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f89,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

fof(f224,plain,
    ( spl5_7
    | spl5_10 ),
    inference(avatar_split_clause,[],[f219,f221,f203])).

fof(f219,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f218,f85])).

fof(f218,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f165,f88])).

fof(f165,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f89,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f74])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
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

fof(f217,plain,
    ( spl5_7
    | spl5_9 ),
    inference(avatar_split_clause,[],[f212,f214,f203])).

fof(f212,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f211,f85])).

fof(f211,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f88])).

fof(f164,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f89,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2(X0,X1),X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f199,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f190,f196,f192])).

fof(f190,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f162,f88])).

fof(f162,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f89,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f149,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f90,f145,f141])).

fof(f90,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f148,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f91,f145,f141])).

fof(f91,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.56  % (16023)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (16038)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (16027)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (16026)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (16051)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (16023)Refutation not found, incomplete strategy% (16023)------------------------------
% 0.21/0.57  % (16023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (16043)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (16047)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (16053)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (16023)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  % (16031)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.55/0.57  % (16025)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.55/0.58  % (16035)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.58  
% 1.55/0.58  % (16023)Memory used [KB]: 1663
% 1.55/0.58  % (16023)Time elapsed: 0.135 s
% 1.55/0.58  % (16023)------------------------------
% 1.55/0.58  % (16023)------------------------------
% 1.55/0.58  % (16049)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.55/0.58  % (16030)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.55/0.58  % (16034)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.58  % (16052)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.55/0.59  % (16027)Refutation not found, incomplete strategy% (16027)------------------------------
% 1.55/0.59  % (16027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (16027)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (16027)Memory used [KB]: 6396
% 1.55/0.59  % (16027)Time elapsed: 0.151 s
% 1.55/0.59  % (16027)------------------------------
% 1.55/0.59  % (16027)------------------------------
% 1.79/0.60  % (16041)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.79/0.60  % (16045)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.79/0.60  % (16037)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.79/0.60  % (16047)Refutation not found, incomplete strategy% (16047)------------------------------
% 1.79/0.60  % (16047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.61  % (16028)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.79/0.61  % (16031)Refutation found. Thanks to Tanya!
% 1.79/0.61  % SZS status Theorem for theBenchmark
% 1.79/0.61  % (16047)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.61  
% 1.79/0.61  % (16047)Memory used [KB]: 10874
% 1.79/0.61  % (16047)Time elapsed: 0.177 s
% 1.79/0.61  % (16047)------------------------------
% 1.79/0.61  % (16047)------------------------------
% 1.79/0.61  % (16029)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.79/0.61  % SZS output start Proof for theBenchmark
% 1.79/0.61  fof(f931,plain,(
% 1.79/0.61    $false),
% 1.79/0.61    inference(avatar_sat_refutation,[],[f148,f149,f199,f217,f224,f358,f506,f517,f532,f537,f538,f540,f582,f715,f757,f759,f896,f906,f930])).
% 1.79/0.61  fof(f930,plain,(
% 1.79/0.61    ~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_10),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f929])).
% 1.79/0.61  fof(f929,plain,(
% 1.79/0.61    $false | (~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f928,f908])).
% 1.79/0.61  fof(f908,plain,(
% 1.79/0.61    v1_subset_1(sK1,sK1) | (~spl5_2 | ~spl5_5 | ~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(backward_demodulation,[],[f147,f904])).
% 1.79/0.61  fof(f904,plain,(
% 1.79/0.61    u1_struct_0(sK0) = sK1 | (~spl5_5 | ~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(backward_demodulation,[],[f194,f903])).
% 1.79/0.61  fof(f903,plain,(
% 1.79/0.61    sK1 = k2_pre_topc(sK0,sK1) | (~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f902,f88])).
% 1.79/0.61  fof(f88,plain,(
% 1.79/0.61    l1_pre_topc(sK0)),
% 1.79/0.61    inference(cnf_transformation,[],[f72])).
% 1.79/0.61  fof(f72,plain,(
% 1.79/0.61    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f69,f71,f70])).
% 1.79/0.61  fof(f70,plain,(
% 1.79/0.61    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f71,plain,(
% 1.79/0.61    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f69,plain,(
% 1.79/0.61    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/0.61    inference(flattening,[],[f68])).
% 1.79/0.61  fof(f68,plain,(
% 1.79/0.61    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/0.61    inference(nnf_transformation,[],[f33])).
% 1.79/0.61  fof(f33,plain,(
% 1.79/0.61    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/0.61    inference(flattening,[],[f32])).
% 1.79/0.61  fof(f32,plain,(
% 1.79/0.61    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f28])).
% 1.79/0.61  fof(f28,negated_conjecture,(
% 1.79/0.61    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.79/0.61    inference(negated_conjecture,[],[f27])).
% 1.79/0.61  fof(f27,conjecture,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 1.79/0.61  fof(f902,plain,(
% 1.79/0.61    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f763,f901])).
% 1.79/0.61  fof(f901,plain,(
% 1.79/0.61    v4_pre_topc(sK1,sK0) | (~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f900,f86])).
% 1.79/0.61  fof(f86,plain,(
% 1.79/0.61    v2_pre_topc(sK0)),
% 1.79/0.61    inference(cnf_transformation,[],[f72])).
% 1.79/0.61  fof(f900,plain,(
% 1.79/0.61    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | (~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f892,f88])).
% 1.79/0.61  fof(f892,plain,(
% 1.79/0.61    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f891,f89])).
% 1.79/0.61  fof(f89,plain,(
% 1.79/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.61    inference(cnf_transformation,[],[f72])).
% 1.79/0.61  fof(f891,plain,(
% 1.79/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f890,f216])).
% 1.79/0.61  fof(f216,plain,(
% 1.79/0.61    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_9),
% 1.79/0.61    inference(avatar_component_clause,[],[f214])).
% 1.79/0.61  fof(f214,plain,(
% 1.79/0.61    spl5_9 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.79/0.61  fof(f890,plain,(
% 1.79/0.61    ~m1_pre_topc(sK2(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(resolution,[],[f858,f787])).
% 1.79/0.61  fof(f787,plain,(
% 1.79/0.61    v1_borsuk_1(sK2(sK0,sK1),sK0) | ~spl5_9),
% 1.79/0.61    inference(subsumption_resolution,[],[f786,f85])).
% 1.79/0.61  fof(f85,plain,(
% 1.79/0.61    ~v2_struct_0(sK0)),
% 1.79/0.61    inference(cnf_transformation,[],[f72])).
% 1.79/0.61  fof(f786,plain,(
% 1.79/0.61    v1_borsuk_1(sK2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~spl5_9),
% 1.79/0.61    inference(subsumption_resolution,[],[f785,f86])).
% 1.79/0.61  fof(f785,plain,(
% 1.79/0.61    v1_borsuk_1(sK2(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_9),
% 1.79/0.61    inference(subsumption_resolution,[],[f784,f87])).
% 1.79/0.61  fof(f87,plain,(
% 1.79/0.61    v1_tdlat_3(sK0)),
% 1.79/0.61    inference(cnf_transformation,[],[f72])).
% 1.79/0.61  fof(f784,plain,(
% 1.79/0.61    v1_borsuk_1(sK2(sK0,sK1),sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_9),
% 1.79/0.61    inference(subsumption_resolution,[],[f781,f88])).
% 1.79/0.61  fof(f781,plain,(
% 1.79/0.61    v1_borsuk_1(sK2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_9),
% 1.79/0.61    inference(resolution,[],[f216,f116])).
% 1.79/0.61  fof(f116,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_borsuk_1(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f54])).
% 1.79/0.61  fof(f54,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.61    inference(flattening,[],[f53])).
% 1.79/0.61  fof(f53,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f31])).
% 1.79/0.61  fof(f31,plain,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 1.79/0.61    inference(pure_predicate_removal,[],[f17])).
% 1.79/0.61  fof(f17,axiom,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 1.79/0.61  fof(f858,plain,(
% 1.79/0.61    ( ! [X14] : (~v1_borsuk_1(sK2(sK0,sK1),X14) | ~m1_pre_topc(sK2(sK0,sK1),X14) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X14))) | v4_pre_topc(sK1,X14) | ~l1_pre_topc(X14) | ~v2_pre_topc(X14)) ) | ~spl5_10),
% 1.79/0.61    inference(superposition,[],[f139,f223])).
% 1.79/0.61  fof(f223,plain,(
% 1.79/0.61    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_10),
% 1.79/0.61    inference(avatar_component_clause,[],[f221])).
% 1.79/0.61  fof(f221,plain,(
% 1.79/0.61    spl5_10 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.79/0.61  fof(f139,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | v4_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.79/0.61    inference(duplicate_literal_removal,[],[f137])).
% 1.79/0.61  fof(f137,plain,(
% 1.79/0.61    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.79/0.61    inference(equality_resolution,[],[f122])).
% 1.79/0.61  fof(f122,plain,(
% 1.79/0.61    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f83])).
% 1.79/0.61  fof(f83,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.61    inference(flattening,[],[f82])).
% 1.79/0.61  fof(f82,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.61    inference(nnf_transformation,[],[f60])).
% 1.79/0.61  fof(f60,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.61    inference(flattening,[],[f59])).
% 1.79/0.61  fof(f59,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f14])).
% 1.79/0.61  fof(f14,axiom,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).
% 1.79/0.61  fof(f763,plain,(
% 1.79/0.61    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f101])).
% 1.79/0.61  fof(f101,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f40])).
% 1.79/0.61  fof(f40,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.61    inference(flattening,[],[f39])).
% 1.79/0.61  fof(f39,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.61    inference(ennf_transformation,[],[f12])).
% 1.79/0.61  fof(f12,axiom,(
% 1.79/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.79/0.61  fof(f194,plain,(
% 1.79/0.61    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl5_5),
% 1.79/0.61    inference(avatar_component_clause,[],[f192])).
% 1.79/0.61  fof(f192,plain,(
% 1.79/0.61    spl5_5 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.79/0.61  fof(f147,plain,(
% 1.79/0.61    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_2),
% 1.79/0.61    inference(avatar_component_clause,[],[f145])).
% 1.79/0.61  fof(f145,plain,(
% 1.79/0.61    spl5_2 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.79/0.61  fof(f928,plain,(
% 1.79/0.61    ~v1_subset_1(sK1,sK1) | (~spl5_5 | ~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(resolution,[],[f907,f138])).
% 1.79/0.61  fof(f138,plain,(
% 1.79/0.61    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.79/0.61    inference(equality_resolution,[],[f127])).
% 1.79/0.61  fof(f127,plain,(
% 1.79/0.61    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f84])).
% 1.79/0.61  fof(f84,plain,(
% 1.79/0.61    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.61    inference(nnf_transformation,[],[f64])).
% 1.79/0.61  fof(f64,plain,(
% 1.79/0.61    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f19])).
% 1.79/0.61  fof(f19,axiom,(
% 1.79/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.79/0.61  fof(f907,plain,(
% 1.79/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl5_5 | ~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(backward_demodulation,[],[f89,f904])).
% 1.79/0.61  fof(f906,plain,(
% 1.79/0.61    ~spl5_5 | ~spl5_9 | ~spl5_10 | spl5_20),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f905])).
% 1.79/0.61  fof(f905,plain,(
% 1.79/0.61    $false | (~spl5_5 | ~spl5_9 | ~spl5_10 | spl5_20)),
% 1.79/0.61    inference(subsumption_resolution,[],[f904,f362])).
% 1.79/0.61  fof(f362,plain,(
% 1.79/0.61    u1_struct_0(sK0) != sK1 | spl5_20),
% 1.79/0.61    inference(avatar_component_clause,[],[f361])).
% 1.79/0.61  fof(f361,plain,(
% 1.79/0.61    spl5_20 <=> u1_struct_0(sK0) = sK1),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.79/0.61  fof(f896,plain,(
% 1.79/0.61    spl5_4 | ~spl5_9 | ~spl5_10),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f895])).
% 1.79/0.61  fof(f895,plain,(
% 1.79/0.61    $false | (spl5_4 | ~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f894,f86])).
% 1.79/0.61  fof(f894,plain,(
% 1.79/0.61    ~v2_pre_topc(sK0) | (spl5_4 | ~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f893,f88])).
% 1.79/0.61  fof(f893,plain,(
% 1.79/0.61    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl5_4 | ~spl5_9 | ~spl5_10)),
% 1.79/0.61    inference(subsumption_resolution,[],[f892,f185])).
% 1.79/0.61  fof(f185,plain,(
% 1.79/0.61    ~v4_pre_topc(sK1,sK0) | spl5_4),
% 1.79/0.61    inference(avatar_component_clause,[],[f183])).
% 1.79/0.61  fof(f183,plain,(
% 1.79/0.61    spl5_4 <=> v4_pre_topc(sK1,sK0)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.79/0.61  fof(f759,plain,(
% 1.79/0.61    spl5_3 | ~spl5_4),
% 1.79/0.61    inference(avatar_split_clause,[],[f758,f183,f179])).
% 1.79/0.61  fof(f179,plain,(
% 1.79/0.61    spl5_3 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.79/0.61  fof(f758,plain,(
% 1.79/0.61    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.79/0.61    inference(subsumption_resolution,[],[f387,f88])).
% 1.79/0.61  fof(f387,plain,(
% 1.79/0.61    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f101])).
% 1.79/0.61  fof(f757,plain,(
% 1.79/0.61    ~spl5_3 | spl5_6 | ~spl5_20),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f756])).
% 1.79/0.61  fof(f756,plain,(
% 1.79/0.61    $false | (~spl5_3 | spl5_6 | ~spl5_20)),
% 1.79/0.61    inference(subsumption_resolution,[],[f755,f560])).
% 1.79/0.61  fof(f560,plain,(
% 1.79/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl5_20),
% 1.79/0.61    inference(backward_demodulation,[],[f89,f363])).
% 1.79/0.61  fof(f363,plain,(
% 1.79/0.61    u1_struct_0(sK0) = sK1 | ~spl5_20),
% 1.79/0.61    inference(avatar_component_clause,[],[f361])).
% 1.79/0.61  fof(f755,plain,(
% 1.79/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl5_3 | spl5_6 | ~spl5_20)),
% 1.79/0.61    inference(forward_demodulation,[],[f754,f363])).
% 1.79/0.61  fof(f754,plain,(
% 1.79/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_3 | spl5_6 | ~spl5_20)),
% 1.79/0.61    inference(subsumption_resolution,[],[f753,f88])).
% 1.79/0.61  fof(f753,plain,(
% 1.79/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_3 | spl5_6 | ~spl5_20)),
% 1.79/0.61    inference(subsumption_resolution,[],[f752,f198])).
% 1.79/0.61  fof(f198,plain,(
% 1.79/0.61    ~v1_tops_1(sK1,sK0) | spl5_6),
% 1.79/0.61    inference(avatar_component_clause,[],[f196])).
% 1.79/0.61  fof(f196,plain,(
% 1.79/0.61    spl5_6 <=> v1_tops_1(sK1,sK0)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.79/0.61  fof(f752,plain,(
% 1.79/0.61    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_3 | ~spl5_20)),
% 1.79/0.61    inference(subsumption_resolution,[],[f751,f363])).
% 1.79/0.61  fof(f751,plain,(
% 1.79/0.61    u1_struct_0(sK0) != sK1 | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_3),
% 1.79/0.61    inference(superposition,[],[f104,f181])).
% 1.79/0.61  fof(f181,plain,(
% 1.79/0.61    sK1 = k2_pre_topc(sK0,sK1) | ~spl5_3),
% 1.79/0.61    inference(avatar_component_clause,[],[f179])).
% 1.79/0.61  fof(f104,plain,(
% 1.79/0.61    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f73])).
% 1.79/0.61  fof(f73,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.61    inference(nnf_transformation,[],[f41])).
% 1.79/0.61  fof(f41,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.61    inference(ennf_transformation,[],[f18])).
% 1.79/0.61  fof(f18,axiom,(
% 1.79/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 1.79/0.61  fof(f715,plain,(
% 1.79/0.61    spl5_6 | ~spl5_20 | ~spl5_23),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f714])).
% 1.79/0.61  fof(f714,plain,(
% 1.79/0.61    $false | (spl5_6 | ~spl5_20 | ~spl5_23)),
% 1.79/0.61    inference(subsumption_resolution,[],[f198,f713])).
% 1.79/0.61  fof(f713,plain,(
% 1.79/0.61    v1_tops_1(sK1,sK0) | (~spl5_20 | ~spl5_23)),
% 1.79/0.61    inference(subsumption_resolution,[],[f712,f560])).
% 1.79/0.61  fof(f712,plain,(
% 1.79/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | v1_tops_1(sK1,sK0) | (~spl5_20 | ~spl5_23)),
% 1.79/0.61    inference(forward_demodulation,[],[f711,f363])).
% 1.79/0.61  fof(f711,plain,(
% 1.79/0.61    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_20 | ~spl5_23)),
% 1.79/0.61    inference(subsumption_resolution,[],[f705,f88])).
% 1.79/0.61  fof(f705,plain,(
% 1.79/0.61    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_20 | ~spl5_23)),
% 1.79/0.61    inference(subsumption_resolution,[],[f704,f363])).
% 1.79/0.61  fof(f704,plain,(
% 1.79/0.61    u1_struct_0(sK0) != sK1 | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl5_20 | ~spl5_23)),
% 1.79/0.61    inference(superposition,[],[f104,f571])).
% 1.79/0.61  fof(f571,plain,(
% 1.79/0.61    sK1 = k2_pre_topc(sK0,sK1) | (~spl5_20 | ~spl5_23)),
% 1.79/0.61    inference(backward_demodulation,[],[f550,f363])).
% 1.79/0.61  fof(f550,plain,(
% 1.79/0.61    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~spl5_23),
% 1.79/0.61    inference(backward_demodulation,[],[f438,f448])).
% 1.79/0.61  fof(f448,plain,(
% 1.79/0.61    u1_struct_0(sK0) = sK3(sK0) | ~spl5_23),
% 1.79/0.61    inference(avatar_component_clause,[],[f446])).
% 1.79/0.61  fof(f446,plain,(
% 1.79/0.61    spl5_23 <=> u1_struct_0(sK0) = sK3(sK0)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.79/0.61  fof(f438,plain,(
% 1.79/0.61    sK3(sK0) = k2_pre_topc(sK0,sK3(sK0))),
% 1.79/0.61    inference(subsumption_resolution,[],[f437,f88])).
% 1.79/0.61  fof(f437,plain,(
% 1.79/0.61    sK3(sK0) = k2_pre_topc(sK0,sK3(sK0)) | ~l1_pre_topc(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f420,f158])).
% 1.79/0.61  fof(f158,plain,(
% 1.79/0.61    v4_pre_topc(sK3(sK0),sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f157,f86])).
% 1.79/0.61  fof(f157,plain,(
% 1.79/0.61    ~v2_pre_topc(sK0) | v4_pre_topc(sK3(sK0),sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f152,f88])).
% 1.79/0.61  fof(f152,plain,(
% 1.79/0.61    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(sK3(sK0),sK0)),
% 1.79/0.61    inference(resolution,[],[f85,f115])).
% 1.79/0.61  fof(f115,plain,(
% 1.79/0.61    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v4_pre_topc(sK3(X0),X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f77])).
% 1.79/0.61  fof(f77,plain,(
% 1.79/0.61    ! [X0] : ((v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f76])).
% 1.79/0.61  fof(f76,plain,(
% 1.79/0.61    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f52,plain,(
% 1.79/0.61    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.61    inference(flattening,[],[f51])).
% 1.79/0.61  fof(f51,plain,(
% 1.79/0.61    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f13])).
% 1.79/0.61  fof(f13,axiom,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).
% 1.79/0.61  fof(f420,plain,(
% 1.79/0.61    ~v4_pre_topc(sK3(sK0),sK0) | sK3(sK0) = k2_pre_topc(sK0,sK3(sK0)) | ~l1_pre_topc(sK0)),
% 1.79/0.61    inference(resolution,[],[f154,f101])).
% 1.79/0.61  fof(f154,plain,(
% 1.79/0.61    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.61    inference(subsumption_resolution,[],[f153,f86])).
% 1.79/0.61  fof(f153,plain,(
% 1.79/0.61    ~v2_pre_topc(sK0) | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.61    inference(subsumption_resolution,[],[f150,f88])).
% 1.79/0.61  fof(f150,plain,(
% 1.79/0.61    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.61    inference(resolution,[],[f85,f112])).
% 1.79/0.61  fof(f112,plain,(
% 1.79/0.61    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.79/0.61    inference(cnf_transformation,[],[f77])).
% 1.79/0.61  fof(f582,plain,(
% 1.79/0.61    spl5_3 | ~spl5_5 | ~spl5_20),
% 1.79/0.61    inference(avatar_contradiction_clause,[],[f581])).
% 1.79/0.61  fof(f581,plain,(
% 1.79/0.61    $false | (spl5_3 | ~spl5_5 | ~spl5_20)),
% 1.79/0.61    inference(subsumption_resolution,[],[f563,f180])).
% 1.79/0.61  fof(f180,plain,(
% 1.79/0.61    sK1 != k2_pre_topc(sK0,sK1) | spl5_3),
% 1.79/0.61    inference(avatar_component_clause,[],[f179])).
% 1.79/0.61  fof(f563,plain,(
% 1.79/0.61    sK1 = k2_pre_topc(sK0,sK1) | (~spl5_5 | ~spl5_20)),
% 1.79/0.61    inference(backward_demodulation,[],[f194,f363])).
% 1.79/0.61  fof(f540,plain,(
% 1.79/0.61    ~spl5_19 | ~spl5_30),
% 1.79/0.61    inference(avatar_split_clause,[],[f435,f498,f355])).
% 1.79/0.61  fof(f355,plain,(
% 1.79/0.61    spl5_19 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.79/0.61  fof(f498,plain,(
% 1.79/0.61    spl5_30 <=> v1_subset_1(sK3(sK0),u1_struct_0(sK0))),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.79/0.61  fof(f435,plain,(
% 1.79/0.61    ~v1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v1_xboole_0(u1_struct_0(sK0))),
% 1.79/0.61    inference(resolution,[],[f154,f105])).
% 1.79/0.61  fof(f105,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f42])).
% 1.79/0.61  fof(f42,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.79/0.61    inference(ennf_transformation,[],[f10])).
% 1.79/0.61  fof(f10,axiom,(
% 1.79/0.61    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 1.79/0.61  fof(f538,plain,(
% 1.79/0.61    spl5_2 | spl5_20),
% 1.79/0.61    inference(avatar_split_clause,[],[f400,f361,f145])).
% 1.79/0.61  fof(f400,plain,(
% 1.79/0.61    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.79/0.61    inference(resolution,[],[f89,f128])).
% 1.79/0.61  fof(f128,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f84])).
% 1.79/0.61  fof(f537,plain,(
% 1.79/0.61    spl5_6 | ~spl5_1),
% 1.79/0.61    inference(avatar_split_clause,[],[f536,f141,f196])).
% 1.79/0.61  fof(f141,plain,(
% 1.79/0.61    spl5_1 <=> v3_tex_2(sK1,sK0)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.79/0.61  fof(f536,plain,(
% 1.79/0.61    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f535,f85])).
% 1.79/0.61  fof(f535,plain,(
% 1.79/0.61    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f534,f86])).
% 1.79/0.61  fof(f534,plain,(
% 1.79/0.61    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f533,f88])).
% 1.79/0.61  fof(f533,plain,(
% 1.79/0.61    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f167,f240])).
% 1.79/0.61  fof(f240,plain,(
% 1.79/0.61    v3_pre_topc(sK1,sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f239,f86])).
% 1.79/0.61  fof(f239,plain,(
% 1.79/0.61    v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f238,f88])).
% 1.79/0.61  fof(f238,plain,(
% 1.79/0.61    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f170,f87])).
% 1.79/0.61  fof(f170,plain,(
% 1.79/0.61    v3_pre_topc(sK1,sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f119])).
% 1.79/0.61  fof(f119,plain,(
% 1.79/0.61    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f81])).
% 1.79/0.61  fof(f81,plain,(
% 1.79/0.61    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f79,f80])).
% 1.79/0.61  fof(f80,plain,(
% 1.79/0.61    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f79,plain,(
% 1.79/0.61    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.61    inference(rectify,[],[f78])).
% 1.79/0.61  fof(f78,plain,(
% 1.79/0.61    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.61    inference(nnf_transformation,[],[f58])).
% 1.79/0.61  fof(f58,plain,(
% 1.79/0.61    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.61    inference(flattening,[],[f57])).
% 1.79/0.61  fof(f57,plain,(
% 1.79/0.61    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f22])).
% 1.79/0.61  fof(f22,axiom,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 1.79/0.61  fof(f167,plain,(
% 1.79/0.61    ~v3_tex_2(sK1,sK0) | ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f110])).
% 1.79/0.61  fof(f110,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | v1_tops_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f48])).
% 1.79/0.61  fof(f48,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.61    inference(flattening,[],[f47])).
% 1.79/0.61  fof(f47,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f25])).
% 1.79/0.61  fof(f25,axiom,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 1.79/0.61  fof(f532,plain,(
% 1.79/0.61    spl5_1 | ~spl5_6),
% 1.79/0.61    inference(avatar_split_clause,[],[f531,f196,f141])).
% 1.79/0.61  fof(f531,plain,(
% 1.79/0.61    ~v1_tops_1(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f530,f85])).
% 1.79/0.61  fof(f530,plain,(
% 1.79/0.61    ~v1_tops_1(sK1,sK0) | v3_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f529,f86])).
% 1.79/0.61  fof(f529,plain,(
% 1.79/0.61    ~v1_tops_1(sK1,sK0) | v3_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f528,f88])).
% 1.79/0.61  fof(f528,plain,(
% 1.79/0.61    ~v1_tops_1(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f166,f237])).
% 1.79/0.61  fof(f237,plain,(
% 1.79/0.61    v2_tex_2(sK1,sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f236,f85])).
% 1.79/0.61  fof(f236,plain,(
% 1.79/0.61    v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f235,f86])).
% 1.79/0.61  fof(f235,plain,(
% 1.79/0.61    v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f234,f87])).
% 1.79/0.61  fof(f234,plain,(
% 1.79/0.61    v2_tex_2(sK1,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f169,f88])).
% 1.79/0.61  fof(f169,plain,(
% 1.79/0.61    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f118])).
% 1.79/0.61  % (16054)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.79/0.61  fof(f118,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f56])).
% 1.79/0.61  fof(f56,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.61    inference(flattening,[],[f55])).
% 1.79/0.61  fof(f55,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f23])).
% 1.79/0.61  fof(f23,axiom,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 1.79/0.61  fof(f166,plain,(
% 1.79/0.61    ~v2_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f109])).
% 1.79/0.61  fof(f109,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f46])).
% 1.79/0.61  fof(f46,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.61    inference(flattening,[],[f45])).
% 1.79/0.61  fof(f45,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f26])).
% 1.79/0.61  fof(f26,axiom,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 1.79/0.61  fof(f517,plain,(
% 1.79/0.61    ~spl5_7 | ~spl5_1),
% 1.79/0.61    inference(avatar_split_clause,[],[f516,f141,f203])).
% 1.79/0.61  fof(f203,plain,(
% 1.79/0.61    spl5_7 <=> v1_xboole_0(sK1)),
% 1.79/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.79/0.61  fof(f516,plain,(
% 1.79/0.61    ~v3_tex_2(sK1,sK0) | ~v1_xboole_0(sK1)),
% 1.79/0.61    inference(subsumption_resolution,[],[f515,f85])).
% 1.79/0.61  fof(f515,plain,(
% 1.79/0.61    ~v3_tex_2(sK1,sK0) | ~v1_xboole_0(sK1) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f514,f86])).
% 1.79/0.61  fof(f514,plain,(
% 1.79/0.61    ~v3_tex_2(sK1,sK0) | ~v1_xboole_0(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f395,f88])).
% 1.79/0.61  fof(f395,plain,(
% 1.79/0.61    ~v3_tex_2(sK1,sK0) | ~v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f111])).
% 1.79/0.61  fof(f111,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f50])).
% 1.79/0.61  fof(f50,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.61    inference(flattening,[],[f49])).
% 1.79/0.61  fof(f49,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f24])).
% 1.79/0.61  fof(f24,axiom,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 1.79/0.61  fof(f506,plain,(
% 1.79/0.61    spl5_30 | spl5_23),
% 1.79/0.61    inference(avatar_split_clause,[],[f433,f446,f498])).
% 1.79/0.61  fof(f433,plain,(
% 1.79/0.61    u1_struct_0(sK0) = sK3(sK0) | v1_subset_1(sK3(sK0),u1_struct_0(sK0))),
% 1.79/0.61    inference(resolution,[],[f154,f128])).
% 1.79/0.61  fof(f358,plain,(
% 1.79/0.61    spl5_19 | spl5_2 | ~spl5_7),
% 1.79/0.61    inference(avatar_split_clause,[],[f353,f203,f145,f355])).
% 1.79/0.61  fof(f353,plain,(
% 1.79/0.61    v1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_7),
% 1.79/0.61    inference(subsumption_resolution,[],[f176,f205])).
% 1.79/0.61  fof(f205,plain,(
% 1.79/0.61    v1_xboole_0(sK1) | ~spl5_7),
% 1.79/0.61    inference(avatar_component_clause,[],[f203])).
% 1.79/0.61  fof(f176,plain,(
% 1.79/0.61    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_xboole_0(sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 1.79/0.61    inference(resolution,[],[f89,f98])).
% 1.79/0.61  fof(f98,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_subset_1(X1,X0) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f35])).
% 1.79/0.61  fof(f35,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.79/0.61    inference(flattening,[],[f34])).
% 1.79/0.61  fof(f34,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.79/0.61    inference(ennf_transformation,[],[f9])).
% 1.79/0.61  fof(f9,axiom,(
% 1.79/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).
% 1.79/0.61  fof(f224,plain,(
% 1.79/0.61    spl5_7 | spl5_10),
% 1.79/0.61    inference(avatar_split_clause,[],[f219,f221,f203])).
% 1.79/0.61  fof(f219,plain,(
% 1.79/0.61    sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 1.79/0.61    inference(subsumption_resolution,[],[f218,f85])).
% 1.79/0.61  fof(f218,plain,(
% 1.79/0.61    sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f165,f88])).
% 1.79/0.61  fof(f165,plain,(
% 1.79/0.61    sK1 = u1_struct_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f108])).
% 1.79/0.61  fof(f108,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1 | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f75])).
% 1.79/0.61  fof(f75,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f74])).
% 1.79/0.61  fof(f74,plain,(
% 1.79/0.61    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & ~v2_struct_0(sK2(X0,X1))))),
% 1.79/0.61    introduced(choice_axiom,[])).
% 1.79/0.61  fof(f44,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.61    inference(flattening,[],[f43])).
% 1.79/0.61  fof(f43,plain,(
% 1.79/0.61    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.61    inference(ennf_transformation,[],[f30])).
% 1.79/0.61  fof(f30,plain,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 1.79/0.61    inference(pure_predicate_removal,[],[f21])).
% 1.79/0.61  fof(f21,axiom,(
% 1.79/0.61    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.79/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 1.79/0.61  fof(f217,plain,(
% 1.79/0.61    spl5_7 | spl5_9),
% 1.79/0.61    inference(avatar_split_clause,[],[f212,f214,f203])).
% 1.79/0.61  fof(f212,plain,(
% 1.79/0.61    m1_pre_topc(sK2(sK0,sK1),sK0) | v1_xboole_0(sK1)),
% 1.79/0.61    inference(subsumption_resolution,[],[f211,f85])).
% 1.79/0.61  fof(f211,plain,(
% 1.79/0.61    m1_pre_topc(sK2(sK0,sK1),sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0)),
% 1.79/0.61    inference(subsumption_resolution,[],[f164,f88])).
% 1.79/0.61  fof(f164,plain,(
% 1.79/0.61    m1_pre_topc(sK2(sK0,sK1),sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f107])).
% 1.79/0.61  fof(f107,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK2(X0,X1),X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f75])).
% 1.79/0.61  fof(f199,plain,(
% 1.79/0.61    spl5_5 | ~spl5_6),
% 1.79/0.61    inference(avatar_split_clause,[],[f190,f196,f192])).
% 1.79/0.61  fof(f190,plain,(
% 1.79/0.61    ~v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.79/0.61    inference(subsumption_resolution,[],[f162,f88])).
% 1.79/0.61  fof(f162,plain,(
% 1.79/0.61    ~v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.79/0.61    inference(resolution,[],[f89,f103])).
% 1.79/0.61  fof(f103,plain,(
% 1.79/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.79/0.61    inference(cnf_transformation,[],[f73])).
% 1.79/0.61  fof(f149,plain,(
% 1.79/0.61    spl5_1 | ~spl5_2),
% 1.79/0.61    inference(avatar_split_clause,[],[f90,f145,f141])).
% 1.79/0.61  fof(f90,plain,(
% 1.79/0.61    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 1.79/0.61    inference(cnf_transformation,[],[f72])).
% 1.79/0.61  fof(f148,plain,(
% 1.79/0.61    ~spl5_1 | spl5_2),
% 1.79/0.61    inference(avatar_split_clause,[],[f91,f145,f141])).
% 1.79/0.61  fof(f91,plain,(
% 1.79/0.61    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 1.79/0.61    inference(cnf_transformation,[],[f72])).
% 1.79/0.61  % SZS output end Proof for theBenchmark
% 1.79/0.61  % (16031)------------------------------
% 1.79/0.61  % (16031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.61  % (16031)Termination reason: Refutation
% 1.79/0.61  
% 1.79/0.61  % (16031)Memory used [KB]: 11001
% 1.79/0.61  % (16031)Time elapsed: 0.181 s
% 1.79/0.61  % (16031)------------------------------
% 1.79/0.61  % (16031)------------------------------
% 1.79/0.62  % (16015)Success in time 0.257 s
%------------------------------------------------------------------------------
