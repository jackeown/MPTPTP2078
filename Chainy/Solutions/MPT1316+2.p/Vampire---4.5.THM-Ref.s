%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1316+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 223 expanded)
%              Number of leaves         :   22 (  93 expanded)
%              Depth                    :   18
%              Number of atoms          :  430 (1161 expanded)
%              Number of equality atoms :   20 ( 103 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2880,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2474,f2478,f2482,f2486,f2490,f2494,f2498,f2507,f2512,f2647,f2662,f2865,f2879])).

fof(f2879,plain,
    ( spl10_9
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_56 ),
    inference(avatar_contradiction_clause,[],[f2878])).

fof(f2878,plain,
    ( $false
    | spl10_9
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f2877,f2506])).

fof(f2506,plain,
    ( ~ v1_tops_2(sK1,sK2)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f2505])).

fof(f2505,plain,
    ( spl10_9
  <=> v1_tops_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f2877,plain,
    ( v1_tops_2(sK1,sK2)
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f2875,f2511])).

fof(f2511,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f2510])).

fof(f2510,plain,
    ( spl10_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f2875,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v1_tops_2(sK1,sK2)
    | ~ spl10_22
    | ~ spl10_56 ),
    inference(resolution,[],[f2864,f2646])).

fof(f2646,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v1_tops_2(X0,sK2) )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f2645])).

fof(f2645,plain,
    ( spl10_22
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v1_tops_2(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f2864,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f2863])).

fof(f2863,plain,
    ( spl10_56
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f2865,plain,
    ( spl10_56
    | ~ spl10_5
    | ~ spl10_7
    | spl10_9
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f2861,f2510,f2505,f2496,f2488,f2863])).

fof(f2488,plain,
    ( spl10_5
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f2496,plain,
    ( spl10_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f2861,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl10_5
    | ~ spl10_7
    | spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f2859,f2506])).

fof(f2859,plain,
    ( v1_tops_2(sK1,sK2)
    | r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f2854,f2511])).

fof(f2854,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v1_tops_2(X0,sK2)
        | r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl10_5
    | ~ spl10_7 ),
    inference(resolution,[],[f2794,f2489])).

fof(f2489,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f2488])).

fof(f2794,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v1_tops_2(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | r2_hidden(sK4(X1,X0),X0) )
    | ~ spl10_7 ),
    inference(resolution,[],[f2542,f2497])).

fof(f2497,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f2496])).

fof(f2542,plain,(
    ! [X4,X2,X3] :
      ( ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2)
      | ~ m1_pre_topc(X2,X4)
      | r2_hidden(sK4(X2,X3),X3) ) ),
    inference(resolution,[],[f2446,f2463])).

fof(f2463,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2409])).

fof(f2409,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f2446,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2418])).

fof(f2418,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2416,f2417])).

fof(f2417,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2416,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2415])).

fof(f2415,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2395])).

fof(f2395,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2394])).

fof(f2394,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2241])).

fof(f2241,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f2662,plain,
    ( ~ spl10_5
    | ~ spl10_7
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f2660])).

fof(f2660,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_7
    | spl10_21 ),
    inference(unit_resulting_resolution,[],[f2497,f2489,f2643,f2463])).

fof(f2643,plain,
    ( ~ l1_pre_topc(sK2)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f2642])).

fof(f2642,plain,
    ( spl10_21
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f2647,plain,
    ( ~ spl10_21
    | spl10_22
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f2640,f2496,f2492,f2488,f2484,f2645,f2642])).

fof(f2484,plain,
    ( spl10_4
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f2492,plain,
    ( spl10_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f2640,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | v1_tops_2(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ l1_pre_topc(sK2) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f2636,f2447])).

fof(f2447,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2418])).

fof(f2636,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | v3_pre_topc(sK4(sK2,X0),sK2)
        | v1_tops_2(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ l1_pre_topc(sK2) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2633,f2445])).

fof(f2445,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2418])).

fof(f2633,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK2) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2626,f2489])).

fof(f2626,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X1,X0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(duplicate_literal_removal,[],[f2625])).

fof(f2625,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X1,X0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(condensation,[],[f2624])).

fof(f2624,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ m1_pre_topc(X4,sK0)
        | v3_pre_topc(X2,X4) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2604,f2573])).

fof(f2573,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,sK0)
        | v3_pre_topc(X0,X1) )
    | ~ spl10_7 ),
    inference(resolution,[],[f2572,f2497])).

fof(f2572,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | v3_pre_topc(X3,X2) ) ),
    inference(subsumption_resolution,[],[f2466,f2462])).

fof(f2462,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f2408])).

fof(f2408,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1832])).

fof(f1832,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f2466,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2450])).

fof(f2450,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2400])).

fof(f2400,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2399])).

fof(f2399,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2367])).

fof(f2367,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f2604,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2591,f2527])).

fof(f2527,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl10_7 ),
    inference(resolution,[],[f2462,f2497])).

fof(f2591,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f2588,f2485])).

fof(f2485,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f2484])).

fof(f2588,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_2(sK1,sK0)
        | ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0) )
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2582,f2493])).

fof(f2493,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f2492])).

fof(f2582,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_2(X1,sK0)
        | ~ r2_hidden(X0,X1)
        | v3_pre_topc(X0,sK0) )
    | ~ spl10_7 ),
    inference(resolution,[],[f2444,f2497])).

fof(f2444,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v3_pre_topc(X3,X0) ) ),
    inference(cnf_transformation,[],[f2418])).

fof(f2512,plain,
    ( spl10_10
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f2508,f2480,f2472,f2510])).

fof(f2472,plain,
    ( spl10_1
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f2480,plain,
    ( spl10_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f2508,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f2481,f2473])).

fof(f2473,plain,
    ( sK1 = sK3
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f2472])).

fof(f2481,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f2480])).

fof(f2507,plain,
    ( ~ spl10_9
    | ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f2503,f2476,f2472,f2505])).

fof(f2476,plain,
    ( spl10_2
  <=> v1_tops_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f2503,plain,
    ( ~ v1_tops_2(sK1,sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(forward_demodulation,[],[f2477,f2473])).

fof(f2477,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f2476])).

fof(f2498,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f2433,f2496])).

fof(f2433,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2414])).

fof(f2414,plain,
    ( ~ v1_tops_2(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & v1_tops_2(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2385,f2413,f2412,f2411,f2410])).

fof(f2410,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v1_tops_2(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
                & v1_tops_2(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2411,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v1_tops_2(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
            & v1_tops_2(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v1_tops_2(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
          & v1_tops_2(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f2412,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v1_tops_2(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
        & v1_tops_2(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v1_tops_2(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & v1_tops_2(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2413,plain,
    ( ? [X3] :
        ( ~ v1_tops_2(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ~ v1_tops_2(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f2385,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2384])).

fof(f2384,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2370])).

fof(f2370,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v1_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2369])).

fof(f2369,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(f2494,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f2434,f2492])).

fof(f2434,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f2414])).

fof(f2490,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f2435,f2488])).

fof(f2435,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f2414])).

fof(f2486,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f2436,f2484])).

fof(f2436,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f2414])).

fof(f2482,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f2437,f2480])).

fof(f2437,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f2414])).

fof(f2478,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f2439,f2476])).

fof(f2439,plain,(
    ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f2414])).

fof(f2474,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f2438,f2472])).

fof(f2438,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f2414])).
%------------------------------------------------------------------------------
