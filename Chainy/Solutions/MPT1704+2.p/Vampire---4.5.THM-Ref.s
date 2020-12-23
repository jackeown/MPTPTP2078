%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1704+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 5.41s
% Output     : Refutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 487 expanded)
%              Number of leaves         :   20 ( 162 expanded)
%              Depth                    :   21
%              Number of atoms          :  599 (5418 expanded)
%              Number of equality atoms :   48 ( 439 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10095,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3848,f3849,f3852,f4333,f4396,f7174,f8418,f10065,f10071,f10077,f10094])).

fof(f10094,plain,
    ( ~ spl45_2
    | spl45_4 ),
    inference(avatar_contradiction_clause,[],[f10093])).

fof(f10093,plain,
    ( $false
    | ~ spl45_2
    | spl45_4 ),
    inference(subsumption_resolution,[],[f10091,f3847])).

fof(f3847,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | spl45_4 ),
    inference(avatar_component_clause,[],[f3845])).

fof(f3845,plain,
    ( spl45_4
  <=> m1_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_4])])).

fof(f10091,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl45_2 ),
    inference(subsumption_resolution,[],[f7337,f3838])).

fof(f3838,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl45_2 ),
    inference(avatar_component_clause,[],[f3837])).

fof(f3837,plain,
    ( spl45_2
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_2])])).

fof(f7337,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4) ),
    inference(superposition,[],[f3873,f3599])).

fof(f3599,plain,(
    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
    inference(cnf_transformation,[],[f3486])).

fof(f3486,plain,
    ( ( ~ m1_pre_topc(sK6,sK4)
      | ~ v1_borsuk_1(sK6,sK4)
      | ~ m1_pre_topc(sK5,sK4)
      | ~ v1_borsuk_1(sK5,sK4) )
    & ( ( m1_pre_topc(sK6,sK4)
        & v1_borsuk_1(sK6,sK4) )
      | ( m1_pre_topc(sK5,sK4)
        & v1_borsuk_1(sK5,sK4) ) )
    & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f3482,f3485,f3484,f3483])).

fof(f3483,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK4)
                | ~ v1_borsuk_1(X2,sK4)
                | ~ m1_pre_topc(X1,sK4)
                | ~ v1_borsuk_1(X1,sK4) )
              & ( ( m1_pre_topc(X2,sK4)
                  & v1_borsuk_1(X2,sK4) )
                | ( m1_pre_topc(X1,sK4)
                  & v1_borsuk_1(X1,sK4) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3484,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK4)
              | ~ v1_borsuk_1(X2,sK4)
              | ~ m1_pre_topc(X1,sK4)
              | ~ v1_borsuk_1(X1,sK4) )
            & ( ( m1_pre_topc(X2,sK4)
                & v1_borsuk_1(X2,sK4) )
              | ( m1_pre_topc(X1,sK4)
                & v1_borsuk_1(X1,sK4) ) )
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK4)
            | ~ v1_borsuk_1(X2,sK4)
            | ~ m1_pre_topc(sK5,sK4)
            | ~ v1_borsuk_1(sK5,sK4) )
          & ( ( m1_pre_topc(X2,sK4)
              & v1_borsuk_1(X2,sK4) )
            | ( m1_pre_topc(sK5,sK4)
              & v1_borsuk_1(sK5,sK4) ) )
          & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f3485,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK4)
          | ~ v1_borsuk_1(X2,sK4)
          | ~ m1_pre_topc(sK5,sK4)
          | ~ v1_borsuk_1(sK5,sK4) )
        & ( ( m1_pre_topc(X2,sK4)
            & v1_borsuk_1(X2,sK4) )
          | ( m1_pre_topc(sK5,sK4)
            & v1_borsuk_1(sK5,sK4) ) )
        & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X2
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK6,sK4)
        | ~ v1_borsuk_1(sK6,sK4)
        | ~ m1_pre_topc(sK5,sK4)
        | ~ v1_borsuk_1(sK5,sK4) )
      & ( ( m1_pre_topc(sK6,sK4)
          & v1_borsuk_1(sK6,sK4) )
        | ( m1_pre_topc(sK5,sK4)
          & v1_borsuk_1(sK5,sK4) ) )
      & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f3482,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3481])).

fof(f3481,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3355])).

fof(f3355,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3354])).

fof(f3354,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3333])).

fof(f3333,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_borsuk_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3332])).

fof(f3332,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).

fof(f3873,plain,(
    ! [X44] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X44),u1_pre_topc(X44)),sK4)
      | ~ m1_pre_topc(X44,sK4) ) ),
    inference(resolution,[],[f3594,f3655])).

fof(f3655,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ),
    inference(cnf_transformation,[],[f3399])).

fof(f3399,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3329])).

fof(f3329,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f3594,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3486])).

fof(f10077,plain,
    ( spl45_3
    | ~ spl45_4
    | ~ spl45_695
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(avatar_split_clause,[],[f10074,f7368,f4326,f10068,f3845,f3841])).

fof(f3841,plain,
    ( spl45_3
  <=> v1_borsuk_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_3])])).

fof(f10068,plain,
    ( spl45_695
  <=> v4_pre_topc(u1_struct_0(sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_695])])).

fof(f4326,plain,
    ( spl45_43
  <=> sK6 = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_43])])).

fof(f7368,plain,
    ( spl45_401
  <=> m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_401])])).

fof(f10074,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK5),sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | v1_borsuk_1(sK6,sK4)
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(subsumption_resolution,[],[f10052,f7369])).

fof(f7369,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl45_401 ),
    inference(avatar_component_clause,[],[f7368])).

fof(f10052,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK5),sK4)
    | ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_pre_topc(sK6,sK4)
    | v1_borsuk_1(sK6,sK4)
    | ~ spl45_43 ),
    inference(superposition,[],[f4019,f7287])).

fof(f7287,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK6)
    | ~ spl45_43 ),
    inference(trivial_inequality_removal,[],[f7286])).

fof(f7286,plain,
    ( sK6 != sK6
    | u1_struct_0(sK5) = u1_struct_0(sK6)
    | ~ spl45_43 ),
    inference(superposition,[],[f4387,f4328])).

fof(f4328,plain,
    ( sK6 = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ spl45_43 ),
    inference(avatar_component_clause,[],[f4326])).

fof(f4387,plain,(
    ! [X4,X5] :
      ( sK6 != g1_pre_topc(X4,X5)
      | u1_struct_0(sK5) = X4 ) ),
    inference(global_subsumption,[],[f4078,f4373])).

fof(f4373,plain,(
    ! [X4,X5] :
      ( sK6 != g1_pre_topc(X4,X5)
      | u1_struct_0(sK5) = X4
      | ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ) ),
    inference(superposition,[],[f3696,f3599])).

fof(f3696,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3422])).

fof(f3422,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1808])).

fof(f1808,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f4078,plain,(
    m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(resolution,[],[f3596,f3781])).

fof(f3781,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f3459])).

fof(f3459,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3596,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f3486])).

fof(f4019,plain,(
    ! [X110] :
      ( ~ v4_pre_topc(u1_struct_0(X110),sK4)
      | ~ m1_subset_1(u1_struct_0(X110),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ m1_pre_topc(X110,sK4)
      | v1_borsuk_1(X110,sK4) ) ),
    inference(subsumption_resolution,[],[f3927,f3593])).

fof(f3593,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3486])).

fof(f3927,plain,(
    ! [X110] :
      ( ~ v4_pre_topc(u1_struct_0(X110),sK4)
      | ~ m1_subset_1(u1_struct_0(X110),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ m1_pre_topc(X110,sK4)
      | v1_borsuk_1(X110,sK4)
      | ~ v2_pre_topc(sK4) ) ),
    inference(resolution,[],[f3594,f3823])).

fof(f3823,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v1_borsuk_1(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3676])).

fof(f3676,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3527])).

fof(f3527,plain,(
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
    inference(flattening,[],[f3526])).

fof(f3526,plain,(
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
    inference(nnf_transformation,[],[f3409])).

fof(f3409,plain,(
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
    inference(flattening,[],[f3408])).

fof(f3408,plain,(
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
    inference(ennf_transformation,[],[f3330])).

fof(f3330,axiom,(
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

fof(f10071,plain,
    ( spl45_695
    | ~ spl45_1
    | ~ spl45_2
    | ~ spl45_401 ),
    inference(avatar_split_clause,[],[f10066,f7368,f3837,f3833,f10068])).

fof(f3833,plain,
    ( spl45_1
  <=> v1_borsuk_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_1])])).

fof(f10066,plain,
    ( ~ v1_borsuk_1(sK5,sK4)
    | v4_pre_topc(u1_struct_0(sK5),sK4)
    | ~ spl45_2
    | ~ spl45_401 ),
    inference(subsumption_resolution,[],[f10053,f3838])).

fof(f10053,plain,
    ( ~ v1_borsuk_1(sK5,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | v4_pre_topc(u1_struct_0(sK5),sK4)
    | ~ spl45_401 ),
    inference(resolution,[],[f4020,f7369])).

fof(f4020,plain,(
    ! [X116] :
      ( ~ m1_subset_1(u1_struct_0(X116),k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v1_borsuk_1(X116,sK4)
      | ~ m1_pre_topc(X116,sK4)
      | v4_pre_topc(u1_struct_0(X116),sK4) ) ),
    inference(subsumption_resolution,[],[f3930,f3593])).

fof(f3930,plain,(
    ! [X116] :
      ( ~ m1_pre_topc(X116,sK4)
      | ~ v1_borsuk_1(X116,sK4)
      | ~ m1_subset_1(u1_struct_0(X116),k1_zfmisc_1(u1_struct_0(sK4)))
      | v4_pre_topc(u1_struct_0(X116),sK4)
      | ~ v2_pre_topc(sK4) ) ),
    inference(resolution,[],[f3594,f3831])).

fof(f3831,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f3824])).

fof(f3824,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3675])).

fof(f3675,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3527])).

fof(f10065,plain,
    ( spl45_1
    | ~ spl45_2
    | ~ spl45_3
    | ~ spl45_4
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(avatar_contradiction_clause,[],[f10064])).

fof(f10064,plain,
    ( $false
    | spl45_1
    | ~ spl45_2
    | ~ spl45_3
    | ~ spl45_4
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(subsumption_resolution,[],[f10063,f3835])).

fof(f3835,plain,
    ( ~ v1_borsuk_1(sK5,sK4)
    | spl45_1 ),
    inference(avatar_component_clause,[],[f3833])).

fof(f10063,plain,
    ( v1_borsuk_1(sK5,sK4)
    | ~ spl45_2
    | ~ spl45_3
    | ~ spl45_4
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(subsumption_resolution,[],[f10062,f3838])).

fof(f10062,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | v1_borsuk_1(sK5,sK4)
    | ~ spl45_3
    | ~ spl45_4
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(subsumption_resolution,[],[f10061,f7369])).

fof(f10061,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_pre_topc(sK5,sK4)
    | v1_borsuk_1(sK5,sK4)
    | ~ spl45_3
    | ~ spl45_4
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(resolution,[],[f10060,f4019])).

fof(f10060,plain,
    ( v4_pre_topc(u1_struct_0(sK5),sK4)
    | ~ spl45_3
    | ~ spl45_4
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(subsumption_resolution,[],[f10059,f3846])).

fof(f3846,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl45_4 ),
    inference(avatar_component_clause,[],[f3845])).

fof(f10059,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | v4_pre_topc(u1_struct_0(sK5),sK4)
    | ~ spl45_3
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(subsumption_resolution,[],[f10058,f3842])).

fof(f3842,plain,
    ( v1_borsuk_1(sK6,sK4)
    | ~ spl45_3 ),
    inference(avatar_component_clause,[],[f3841])).

fof(f10058,plain,
    ( ~ v1_borsuk_1(sK6,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | v4_pre_topc(u1_struct_0(sK5),sK4)
    | ~ spl45_43
    | ~ spl45_401 ),
    inference(subsumption_resolution,[],[f10055,f7369])).

fof(f10055,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_borsuk_1(sK6,sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | v4_pre_topc(u1_struct_0(sK5),sK4)
    | ~ spl45_43 ),
    inference(superposition,[],[f4020,f7287])).

fof(f8418,plain,
    ( ~ spl45_2
    | spl45_401 ),
    inference(avatar_contradiction_clause,[],[f8417])).

fof(f8417,plain,
    ( $false
    | ~ spl45_2
    | spl45_401 ),
    inference(subsumption_resolution,[],[f8416,f3594])).

fof(f8416,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ spl45_2
    | spl45_401 ),
    inference(subsumption_resolution,[],[f8415,f3838])).

fof(f8415,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | spl45_401 ),
    inference(resolution,[],[f7370,f3656])).

fof(f3656,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3400])).

fof(f3400,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3334])).

fof(f3334,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f7370,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | spl45_401 ),
    inference(avatar_component_clause,[],[f7368])).

fof(f7174,plain,
    ( spl45_2
    | ~ spl45_4 ),
    inference(avatar_contradiction_clause,[],[f7173])).

fof(f7173,plain,
    ( $false
    | spl45_2
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f7172,f3594])).

fof(f7172,plain,
    ( ~ l1_pre_topc(sK4)
    | spl45_2
    | ~ spl45_4 ),
    inference(subsumption_resolution,[],[f7171,f3839])).

fof(f3839,plain,
    ( ~ m1_pre_topc(sK5,sK4)
    | spl45_2 ),
    inference(avatar_component_clause,[],[f3837])).

fof(f7171,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ spl45_4 ),
    inference(resolution,[],[f4382,f3846])).

fof(f4382,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK6,X0)
      | m1_pre_topc(sK5,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f4381,f3598])).

fof(f3598,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f3486])).

fof(f4381,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK6,X0)
      | ~ l1_pre_topc(sK6)
      | m1_pre_topc(sK5,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f4380,f3595])).

fof(f3595,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f3486])).

fof(f4380,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK6,X0)
      | ~ v2_pre_topc(sK5)
      | ~ l1_pre_topc(sK6)
      | m1_pre_topc(sK5,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f4379,f3596])).

fof(f4379,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK6,X0)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | ~ l1_pre_topc(sK6)
      | m1_pre_topc(sK5,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f4370,f3597])).

fof(f3597,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f3486])).

fof(f4370,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK6)
      | ~ m1_pre_topc(sK6,X0)
      | ~ l1_pre_topc(sK5)
      | ~ v2_pre_topc(sK5)
      | ~ l1_pre_topc(sK6)
      | m1_pre_topc(sK5,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f3808,f3599])).

fof(f3808,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3628])).

fof(f3628,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3501])).

fof(f3501,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3377])).

fof(f3377,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3376])).

fof(f3376,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3331])).

fof(f3331,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f4396,plain,(
    spl45_44 ),
    inference(avatar_contradiction_clause,[],[f4395])).

fof(f4395,plain,
    ( $false
    | spl45_44 ),
    inference(subsumption_resolution,[],[f4378,f4332])).

fof(f4332,plain,
    ( ~ v1_pre_topc(sK6)
    | spl45_44 ),
    inference(avatar_component_clause,[],[f4330])).

fof(f4330,plain,
    ( spl45_44
  <=> v1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_44])])).

fof(f4378,plain,(
    v1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f4377,f3595])).

fof(f4377,plain,
    ( v1_pre_topc(sK6)
    | ~ v2_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f4369,f3596])).

fof(f4369,plain,
    ( v1_pre_topc(sK6)
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(superposition,[],[f3708,f3599])).

fof(f3708,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3429,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3428])).

fof(f3428,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1801])).

fof(f1801,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f4333,plain,
    ( spl45_43
    | ~ spl45_44 ),
    inference(avatar_split_clause,[],[f4233,f4330,f4326])).

fof(f4233,plain,
    ( ~ v1_pre_topc(sK6)
    | sK6 = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(resolution,[],[f3598,f3722])).

fof(f3722,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f3441])).

fof(f3441,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3440])).

fof(f3440,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f3852,plain,
    ( spl45_1
    | spl45_3 ),
    inference(avatar_split_clause,[],[f3600,f3841,f3833])).

fof(f3600,plain,
    ( v1_borsuk_1(sK6,sK4)
    | v1_borsuk_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f3486])).

fof(f3849,plain,
    ( spl45_2
    | spl45_4 ),
    inference(avatar_split_clause,[],[f3603,f3845,f3837])).

fof(f3603,plain,
    ( m1_pre_topc(sK6,sK4)
    | m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f3486])).

fof(f3848,plain,
    ( ~ spl45_1
    | ~ spl45_2
    | ~ spl45_3
    | ~ spl45_4 ),
    inference(avatar_split_clause,[],[f3604,f3845,f3841,f3837,f3833])).

fof(f3604,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ v1_borsuk_1(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ v1_borsuk_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f3486])).
%------------------------------------------------------------------------------
