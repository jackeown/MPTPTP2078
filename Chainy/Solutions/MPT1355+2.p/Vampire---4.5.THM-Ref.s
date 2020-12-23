%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1355+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:19 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 408 expanded)
%              Number of leaves         :   30 ( 189 expanded)
%              Depth                    :   14
%              Number of atoms          :  689 (2513 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3447,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2613,f2614,f2619,f2636,f2657,f2669,f2721,f2727,f2747,f2767,f2937,f2945,f2956,f2966,f2971,f2976,f3122,f3234,f3239,f3389,f3436])).

fof(f3436,plain,
    ( ~ spl14_42
    | spl14_1
    | ~ spl14_3
    | ~ spl14_11
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_23
    | ~ spl14_26 ),
    inference(avatar_split_clause,[],[f3435,f2764,f2744,f2724,f2718,f2666,f2616,f2606,f2934])).

fof(f2934,plain,
    ( spl14_42
  <=> r1_tarski(sK4(sK2,u1_struct_0(sK2),sK11(sK2)),sK11(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_42])])).

fof(f2606,plain,
    ( spl14_1
  <=> v1_compts_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f2616,plain,
    ( spl14_3
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f2666,plain,
    ( spl14_11
  <=> v2_compts_1(u1_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f2718,plain,
    ( spl14_19
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_19])])).

fof(f2724,plain,
    ( spl14_20
  <=> v1_tops_2(sK11(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f2744,plain,
    ( spl14_23
  <=> m1_setfam_1(sK11(sK2),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_23])])).

fof(f2764,plain,
    ( spl14_26
  <=> m1_subset_1(sK11(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f3435,plain,
    ( ~ r1_tarski(sK4(sK2,u1_struct_0(sK2),sK11(sK2)),sK11(sK2))
    | spl14_1
    | ~ spl14_3
    | ~ spl14_11
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_23
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f2608,f2618,f2668,f2746,f2720,f2766,f2726,f3154])).

fof(f3154,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(X1,u1_struct_0(X1),X0),sK11(X1))
      | ~ v2_compts_1(u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v1_compts_1(X1)
      | ~ v1_tops_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_setfam_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f3153])).

fof(f3153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v2_compts_1(u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v1_compts_1(X1)
      | ~ v1_tops_2(X0,X1)
      | ~ r1_tarski(sK4(X1,u1_struct_0(X1),X0),sK11(X1))
      | ~ m1_setfam_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v1_tops_2(X0,X1)
      | ~ m1_setfam_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v2_compts_1(u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f3031,f2539])).

fof(f2539,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2508])).

fof(f2508,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ( ! [X3] :
                    ( ~ v1_finset_1(X3)
                    | ~ m1_setfam_1(X3,X1)
                    | ~ r1_tarski(X3,sK3(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & v1_tops_2(sK3(X0,X1),X0)
                & m1_setfam_1(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ( v1_finset_1(sK4(X0,X1,X4))
                    & m1_setfam_1(sK4(X0,X1,X4),X1)
                    & r1_tarski(sK4(X0,X1,X4),X4)
                    & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f2505,f2507,f2506])).

fof(f2506,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ v1_finset_1(X3)
              | ~ m1_setfam_1(X3,X1)
              | ~ r1_tarski(X3,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X2,X0)
          & m1_setfam_1(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X3] :
            ( ~ v1_finset_1(X3)
            | ~ m1_setfam_1(X3,X1)
            | ~ r1_tarski(X3,sK3(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK3(X0,X1),X0)
        & m1_setfam_1(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2507,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( v1_finset_1(X5)
          & m1_setfam_1(X5,X1)
          & r1_tarski(X5,X4)
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK4(X0,X1,X4))
        & m1_setfam_1(sK4(X0,X1,X4),X1)
        & r1_tarski(sK4(X0,X1,X4),X4)
        & m1_subset_1(sK4(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2505,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( v1_finset_1(X5)
                      & m1_setfam_1(X5,X1)
                      & r1_tarski(X5,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2504])).

fof(f2504,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( v1_finset_1(X3)
                      & m1_setfam_1(X3,X1)
                      & r1_tarski(X3,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X2,X0)
                  | ~ m1_setfam_1(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2468])).

fof(f2468,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2467])).

fof(f2467,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2440])).

fof(f2440,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ~ ( v1_finset_1(X3)
                            & m1_setfam_1(X3,X1)
                            & r1_tarski(X3,X2) ) )
                    & v1_tops_2(X2,X0)
                    & m1_setfam_1(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_compts_1)).

fof(f3031,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4(X2,u1_struct_0(X1),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v2_compts_1(u1_struct_0(X1),X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v1_compts_1(X1)
      | ~ v1_tops_2(X0,X2)
      | ~ r1_tarski(sK4(X2,u1_struct_0(X1),X0),sK11(X1))
      | ~ m1_setfam_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f3030])).

fof(f3030,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_setfam_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v2_compts_1(u1_struct_0(X1),X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | v1_compts_1(X1)
      | ~ v1_tops_2(X0,X2)
      | ~ r1_tarski(sK4(X2,u1_struct_0(X1),X0),sK11(X1))
      | ~ m1_subset_1(sK4(X2,u1_struct_0(X1),X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_tops_2(X0,X2)
      | ~ m1_setfam_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v2_compts_1(u1_struct_0(X1),X2)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f2830,f2541])).

fof(f2541,plain,(
    ! [X4,X0,X1] :
      ( m1_setfam_1(sK4(X0,X1,X4),X1)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2508])).

fof(f2830,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_setfam_1(sK4(X6,X7,X5),u1_struct_0(X8))
      | ~ m1_setfam_1(X5,X7)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
      | ~ v2_compts_1(X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | v1_compts_1(X8)
      | ~ v1_tops_2(X5,X6)
      | ~ r1_tarski(sK4(X6,X7,X5),sK11(X8))
      | ~ m1_subset_1(sK4(X6,X7,X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
      | ~ l1_pre_topc(X8) ) ),
    inference(resolution,[],[f2542,f2596])).

fof(f2596,plain,(
    ! [X2,X0] :
      ( ~ v1_finset_1(X2)
      | v1_compts_1(X0)
      | ~ m1_setfam_1(X2,u1_struct_0(X0))
      | ~ r1_tarski(X2,sK11(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2533])).

fof(f2533,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ( ! [X2] :
                ( ~ v1_finset_1(X2)
                | ~ m1_setfam_1(X2,u1_struct_0(X0))
                | ~ r1_tarski(X2,sK11(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & v1_tops_2(sK11(X0),X0)
            & m1_setfam_1(sK11(X0),u1_struct_0(X0))
            & m1_subset_1(sK11(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X3] :
              ( ( v1_finset_1(sK12(X0,X3))
                & m1_setfam_1(sK12(X0,X3),u1_struct_0(X0))
                & r1_tarski(sK12(X0,X3),X3)
                & m1_subset_1(sK12(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X3,X0)
              | ~ m1_setfam_1(X3,u1_struct_0(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f2530,f2532,f2531])).

fof(f2531,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v1_finset_1(X2)
              | ~ m1_setfam_1(X2,u1_struct_0(X0))
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X1,X0)
          & m1_setfam_1(X1,u1_struct_0(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X2] :
            ( ~ v1_finset_1(X2)
            | ~ m1_setfam_1(X2,u1_struct_0(X0))
            | ~ r1_tarski(X2,sK11(X0))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK11(X0),X0)
        & m1_setfam_1(sK11(X0),u1_struct_0(X0))
        & m1_subset_1(sK11(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2532,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( v1_finset_1(X4)
          & m1_setfam_1(X4,u1_struct_0(X0))
          & r1_tarski(X4,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK12(X0,X3))
        & m1_setfam_1(sK12(X0,X3),u1_struct_0(X0))
        & r1_tarski(sK12(X0,X3),X3)
        & m1_subset_1(sK12(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2530,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ v1_finset_1(X2)
                  | ~ m1_setfam_1(X2,u1_struct_0(X0))
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & v1_tops_2(X1,X0)
              & m1_setfam_1(X1,u1_struct_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( v1_finset_1(X4)
                  & m1_setfam_1(X4,u1_struct_0(X0))
                  & r1_tarski(X4,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X3,X0)
              | ~ m1_setfam_1(X3,u1_struct_0(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2529])).

fof(f2529,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ v1_finset_1(X2)
                  | ~ m1_setfam_1(X2,u1_struct_0(X0))
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              & v1_tops_2(X1,X0)
              & m1_setfam_1(X1,u1_struct_0(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( v1_finset_1(X2)
                  & m1_setfam_1(X2,u1_struct_0(X0))
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_setfam_1(X1,u1_struct_0(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2495])).

fof(f2495,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2494])).

fof(f2494,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( v1_finset_1(X2)
                & m1_setfam_1(X2,u1_struct_0(X0))
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            | ~ v1_tops_2(X1,X0)
            | ~ m1_setfam_1(X1,u1_struct_0(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2439])).

fof(f2439,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                   => ~ ( v1_finset_1(X2)
                        & m1_setfam_1(X2,u1_struct_0(X0))
                        & r1_tarski(X2,X1) ) )
                & v1_tops_2(X1,X0)
                & m1_setfam_1(X1,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_compts_1)).

fof(f2542,plain,(
    ! [X4,X0,X1] :
      ( v1_finset_1(sK4(X0,X1,X4))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2508])).

fof(f2726,plain,
    ( v1_tops_2(sK11(sK2),sK2)
    | ~ spl14_20 ),
    inference(avatar_component_clause,[],[f2724])).

fof(f2766,plain,
    ( m1_subset_1(sK11(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl14_26 ),
    inference(avatar_component_clause,[],[f2764])).

fof(f2720,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_19 ),
    inference(avatar_component_clause,[],[f2718])).

fof(f2746,plain,
    ( m1_setfam_1(sK11(sK2),u1_struct_0(sK2))
    | ~ spl14_23 ),
    inference(avatar_component_clause,[],[f2744])).

fof(f2668,plain,
    ( v2_compts_1(u1_struct_0(sK2),sK2)
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f2666])).

fof(f2618,plain,
    ( l1_pre_topc(sK2)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f2616])).

fof(f2608,plain,
    ( ~ v1_compts_1(sK2)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f2606])).

fof(f3389,plain,
    ( ~ spl14_73
    | spl14_11
    | ~ spl14_19
    | ~ spl14_46
    | ~ spl14_47
    | ~ spl14_48
    | ~ spl14_60
    | ~ spl14_72 ),
    inference(avatar_split_clause,[],[f3387,f3231,f3120,f2973,f2968,f2963,f2718,f2666,f3236])).

fof(f3236,plain,
    ( spl14_73
  <=> r1_tarski(sK12(sK2,sK3(sK2,u1_struct_0(sK2))),sK3(sK2,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_73])])).

fof(f2963,plain,
    ( spl14_46
  <=> m1_setfam_1(sK3(sK2,u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_46])])).

fof(f2968,plain,
    ( spl14_47
  <=> v1_tops_2(sK3(sK2,u1_struct_0(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_47])])).

fof(f2973,plain,
    ( spl14_48
  <=> m1_subset_1(sK3(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).

fof(f3120,plain,
    ( spl14_60
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v1_tops_2(X0,sK2)
        | ~ r1_tarski(sK12(sK2,X0),sK3(sK2,X1))
        | ~ m1_setfam_1(sK12(sK2,X0),X1)
        | v2_compts_1(X1,sK2)
        | ~ m1_setfam_1(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_60])])).

fof(f3231,plain,
    ( spl14_72
  <=> m1_setfam_1(sK12(sK2,sK3(sK2,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_72])])).

fof(f3387,plain,
    ( ~ r1_tarski(sK12(sK2,sK3(sK2,u1_struct_0(sK2))),sK3(sK2,u1_struct_0(sK2)))
    | spl14_11
    | ~ spl14_19
    | ~ spl14_46
    | ~ spl14_47
    | ~ spl14_48
    | ~ spl14_60
    | ~ spl14_72 ),
    inference(unit_resulting_resolution,[],[f2667,f2970,f2720,f2965,f2975,f3233,f3121])).

fof(f3121,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK12(sK2,X0),sK3(sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v1_tops_2(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ m1_setfam_1(sK12(sK2,X0),X1)
        | v2_compts_1(X1,sK2)
        | ~ m1_setfam_1(X0,u1_struct_0(sK2)) )
    | ~ spl14_60 ),
    inference(avatar_component_clause,[],[f3120])).

fof(f3233,plain,
    ( m1_setfam_1(sK12(sK2,sK3(sK2,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl14_72 ),
    inference(avatar_component_clause,[],[f3231])).

fof(f2975,plain,
    ( m1_subset_1(sK3(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl14_48 ),
    inference(avatar_component_clause,[],[f2973])).

fof(f2965,plain,
    ( m1_setfam_1(sK3(sK2,u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl14_46 ),
    inference(avatar_component_clause,[],[f2963])).

fof(f2970,plain,
    ( v1_tops_2(sK3(sK2,u1_struct_0(sK2)),sK2)
    | ~ spl14_47 ),
    inference(avatar_component_clause,[],[f2968])).

fof(f2667,plain,
    ( ~ v2_compts_1(u1_struct_0(sK2),sK2)
    | spl14_11 ),
    inference(avatar_component_clause,[],[f2666])).

fof(f3239,plain,
    ( spl14_73
    | ~ spl14_1
    | ~ spl14_3
    | ~ spl14_46
    | ~ spl14_47
    | ~ spl14_48 ),
    inference(avatar_split_clause,[],[f3222,f2973,f2968,f2963,f2616,f2606,f3236])).

fof(f3222,plain,
    ( r1_tarski(sK12(sK2,sK3(sK2,u1_struct_0(sK2))),sK3(sK2,u1_struct_0(sK2)))
    | ~ spl14_1
    | ~ spl14_3
    | ~ spl14_46
    | ~ spl14_47
    | ~ spl14_48 ),
    inference(unit_resulting_resolution,[],[f2618,f2607,f2970,f2965,f2975,f2590])).

fof(f2590,plain,(
    ! [X0,X3] :
      ( ~ v1_compts_1(X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(sK12(X0,X3),X3)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2533])).

fof(f2607,plain,
    ( v1_compts_1(sK2)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f2606])).

fof(f3234,plain,
    ( spl14_72
    | ~ spl14_1
    | ~ spl14_3
    | ~ spl14_46
    | ~ spl14_47
    | ~ spl14_48 ),
    inference(avatar_split_clause,[],[f3223,f2973,f2968,f2963,f2616,f2606,f3231])).

fof(f3223,plain,
    ( m1_setfam_1(sK12(sK2,sK3(sK2,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl14_1
    | ~ spl14_3
    | ~ spl14_46
    | ~ spl14_47
    | ~ spl14_48 ),
    inference(unit_resulting_resolution,[],[f2618,f2607,f2970,f2965,f2975,f2591])).

fof(f2591,plain,(
    ! [X0,X3] :
      ( m1_setfam_1(sK12(X0,X3),u1_struct_0(X0))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2533])).

fof(f3122,plain,
    ( ~ spl14_1
    | ~ spl14_3
    | spl14_60
    | ~ spl14_45 ),
    inference(avatar_split_clause,[],[f3118,f2954,f3120,f2616,f2606])).

fof(f2954,plain,
    ( spl14_45
  <=> ! [X1] :
        ( ~ v1_tops_2(X1,sK2)
        | v1_finset_1(sK12(sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ m1_setfam_1(X1,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_45])])).

fof(f3118,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ m1_setfam_1(X0,u1_struct_0(sK2))
        | v2_compts_1(X1,sK2)
        | ~ m1_setfam_1(sK12(sK2,X0),X1)
        | ~ r1_tarski(sK12(sK2,X0),sK3(sK2,X1))
        | ~ v1_tops_2(X0,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2)
        | ~ v1_compts_1(sK2) )
    | ~ spl14_45 ),
    inference(duplicate_literal_removal,[],[f3117])).

fof(f3117,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ m1_setfam_1(X0,u1_struct_0(sK2))
        | v2_compts_1(X1,sK2)
        | ~ m1_setfam_1(sK12(sK2,X0),X1)
        | ~ r1_tarski(sK12(sK2,X0),sK3(sK2,X1))
        | ~ v1_tops_2(X0,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2)
        | ~ v1_tops_2(X0,sK2)
        | ~ m1_setfam_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ v1_compts_1(sK2)
        | ~ l1_pre_topc(sK2) )
    | ~ spl14_45 ),
    inference(resolution,[],[f2979,f2589])).

fof(f2589,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK12(X0,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2533])).

fof(f2979,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK12(sK2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ m1_setfam_1(X0,u1_struct_0(sK2))
        | v2_compts_1(X1,X2)
        | ~ m1_setfam_1(sK12(sK2,X0),X1)
        | ~ r1_tarski(sK12(sK2,X0),sK3(X2,X1))
        | ~ v1_tops_2(X0,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2) )
    | ~ spl14_45 ),
    inference(resolution,[],[f2955,f2546])).

fof(f2546,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_finset_1(X3)
      | v2_compts_1(X1,X0)
      | ~ m1_setfam_1(X3,X1)
      | ~ r1_tarski(X3,sK3(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2508])).

fof(f2955,plain,
    ( ! [X1] :
        ( v1_finset_1(sK12(sK2,X1))
        | ~ v1_tops_2(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ m1_setfam_1(X1,u1_struct_0(sK2)) )
    | ~ spl14_45 ),
    inference(avatar_component_clause,[],[f2954])).

fof(f2976,plain,
    ( spl14_48
    | ~ spl14_3
    | spl14_11
    | ~ spl14_19 ),
    inference(avatar_split_clause,[],[f2957,f2718,f2666,f2616,f2973])).

fof(f2957,plain,
    ( m1_subset_1(sK3(sK2,u1_struct_0(sK2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl14_3
    | spl14_11
    | ~ spl14_19 ),
    inference(unit_resulting_resolution,[],[f2618,f2720,f2667,f2543])).

fof(f2543,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2508])).

fof(f2971,plain,
    ( spl14_47
    | ~ spl14_3
    | spl14_11
    | ~ spl14_19 ),
    inference(avatar_split_clause,[],[f2958,f2718,f2666,f2616,f2968])).

fof(f2958,plain,
    ( v1_tops_2(sK3(sK2,u1_struct_0(sK2)),sK2)
    | ~ spl14_3
    | spl14_11
    | ~ spl14_19 ),
    inference(unit_resulting_resolution,[],[f2618,f2720,f2667,f2545])).

fof(f2545,plain,(
    ! [X0,X1] :
      ( v1_tops_2(sK3(X0,X1),X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2508])).

fof(f2966,plain,
    ( spl14_46
    | ~ spl14_3
    | spl14_11
    | ~ spl14_19 ),
    inference(avatar_split_clause,[],[f2959,f2718,f2666,f2616,f2963])).

fof(f2959,plain,
    ( m1_setfam_1(sK3(sK2,u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl14_3
    | spl14_11
    | ~ spl14_19 ),
    inference(unit_resulting_resolution,[],[f2618,f2720,f2667,f2544])).

fof(f2544,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(sK3(X0,X1),X1)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2508])).

fof(f2956,plain,
    ( ~ spl14_3
    | spl14_45
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f2948,f2606,f2954,f2616])).

fof(f2948,plain,
    ( ! [X1] :
        ( ~ v1_tops_2(X1,sK2)
        | ~ m1_setfam_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v1_finset_1(sK12(sK2,X1))
        | ~ l1_pre_topc(sK2) )
    | ~ spl14_1 ),
    inference(resolution,[],[f2607,f2592])).

fof(f2592,plain,(
    ! [X0,X3] :
      ( ~ v1_compts_1(X0)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_setfam_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_finset_1(sK12(X0,X3))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2533])).

fof(f2945,plain,
    ( k2_struct_0(sK2) != u1_struct_0(sK2)
    | v2_compts_1(k2_struct_0(sK2),sK2)
    | ~ v2_compts_1(u1_struct_0(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2937,plain,
    ( spl14_42
    | ~ spl14_3
    | ~ spl14_11
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_23
    | ~ spl14_26 ),
    inference(avatar_split_clause,[],[f2907,f2764,f2744,f2724,f2718,f2666,f2616,f2934])).

fof(f2907,plain,
    ( r1_tarski(sK4(sK2,u1_struct_0(sK2),sK11(sK2)),sK11(sK2))
    | ~ spl14_3
    | ~ spl14_11
    | ~ spl14_19
    | ~ spl14_20
    | ~ spl14_23
    | ~ spl14_26 ),
    inference(unit_resulting_resolution,[],[f2618,f2726,f2668,f2746,f2766,f2720,f2540])).

fof(f2540,plain,(
    ! [X4,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X4),X4)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2508])).

fof(f2767,plain,
    ( spl14_26
    | spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f2762,f2616,f2606,f2764])).

fof(f2762,plain,
    ( m1_subset_1(sK11(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | spl14_1
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f2618,f2608,f2593])).

fof(f2593,plain,(
    ! [X0] :
      ( m1_subset_1(sK11(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2533])).

fof(f2747,plain,
    ( spl14_23
    | spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f2742,f2616,f2606,f2744])).

fof(f2742,plain,
    ( m1_setfam_1(sK11(sK2),u1_struct_0(sK2))
    | spl14_1
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f2618,f2608,f2594])).

fof(f2594,plain,(
    ! [X0] :
      ( m1_setfam_1(sK11(X0),u1_struct_0(X0))
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2533])).

fof(f2727,plain,
    ( spl14_20
    | spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f2722,f2616,f2606,f2724])).

fof(f2722,plain,
    ( v1_tops_2(sK11(sK2),sK2)
    | spl14_1
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f2618,f2608,f2595])).

fof(f2595,plain,(
    ! [X0] :
      ( v1_tops_2(sK11(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2533])).

fof(f2721,plain,
    ( spl14_19
    | ~ spl14_6
    | ~ spl14_9 ),
    inference(avatar_split_clause,[],[f2716,f2653,f2633,f2718])).

fof(f2633,plain,
    ( spl14_6
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f2653,plain,
    ( spl14_9
  <=> k2_struct_0(sK2) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f2716,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_6
    | ~ spl14_9 ),
    inference(forward_demodulation,[],[f2708,f2655])).

fof(f2655,plain,
    ( k2_struct_0(sK2) = u1_struct_0(sK2)
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f2653])).

fof(f2708,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl14_6 ),
    inference(unit_resulting_resolution,[],[f2635,f2555])).

fof(f2555,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2479])).

fof(f2479,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1781])).

fof(f1781,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f2635,plain,
    ( l1_struct_0(sK2)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f2633])).

fof(f2669,plain,
    ( spl14_11
    | ~ spl14_2
    | ~ spl14_9 ),
    inference(avatar_split_clause,[],[f2659,f2653,f2610,f2666])).

fof(f2610,plain,
    ( spl14_2
  <=> v2_compts_1(k2_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f2659,plain,
    ( v2_compts_1(u1_struct_0(sK2),sK2)
    | ~ spl14_2
    | ~ spl14_9 ),
    inference(backward_demodulation,[],[f2611,f2655])).

fof(f2611,plain,
    ( v2_compts_1(k2_struct_0(sK2),sK2)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f2610])).

fof(f2657,plain,
    ( spl14_9
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f2651,f2633,f2653])).

fof(f2651,plain,
    ( k2_struct_0(sK2) = u1_struct_0(sK2)
    | ~ spl14_6 ),
    inference(resolution,[],[f2556,f2635])).

fof(f2556,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2480])).

fof(f2480,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f2636,plain,
    ( spl14_6
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f2625,f2616,f2633])).

fof(f2625,plain,
    ( l1_struct_0(sK2)
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f2618,f2598])).

fof(f2598,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2496])).

fof(f2496,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2619,plain,(
    spl14_3 ),
    inference(avatar_split_clause,[],[f2536,f2616])).

fof(f2536,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2503])).

fof(f2503,plain,
    ( ( ~ v2_compts_1(k2_struct_0(sK2),sK2)
      | ~ v1_compts_1(sK2) )
    & ( v2_compts_1(k2_struct_0(sK2),sK2)
      | v1_compts_1(sK2) )
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f2501,f2502])).

fof(f2502,plain,
    ( ? [X0] :
        ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | v1_compts_1(X0) )
        & l1_pre_topc(X0) )
   => ( ( ~ v2_compts_1(k2_struct_0(sK2),sK2)
        | ~ v1_compts_1(sK2) )
      & ( v2_compts_1(k2_struct_0(sK2),sK2)
        | v1_compts_1(sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2501,plain,(
    ? [X0] :
      ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
        | ~ v1_compts_1(X0) )
      & ( v2_compts_1(k2_struct_0(X0),X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2500])).

fof(f2500,plain,(
    ? [X0] :
      ( ( ~ v2_compts_1(k2_struct_0(X0),X0)
        | ~ v1_compts_1(X0) )
      & ( v2_compts_1(k2_struct_0(X0),X0)
        | v1_compts_1(X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2466])).

fof(f2466,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> v2_compts_1(k2_struct_0(X0),X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2442])).

fof(f2442,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v1_compts_1(X0)
        <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    inference(negated_conjecture,[],[f2441])).

fof(f2441,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(f2614,plain,
    ( spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f2537,f2610,f2606])).

fof(f2537,plain,
    ( v2_compts_1(k2_struct_0(sK2),sK2)
    | v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f2503])).

fof(f2613,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f2538,f2610,f2606])).

fof(f2538,plain,
    ( ~ v2_compts_1(k2_struct_0(sK2),sK2)
    | ~ v1_compts_1(sK2) ),
    inference(cnf_transformation,[],[f2503])).
%------------------------------------------------------------------------------
