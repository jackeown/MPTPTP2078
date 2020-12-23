%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1317+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
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
fof(f2971,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2483,f2487,f2491,f2495,f2499,f2503,f2507,f2516,f2521,f2673,f2688,f2955,f2970])).

fof(f2970,plain,
    ( spl10_9
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_66 ),
    inference(avatar_contradiction_clause,[],[f2969])).

fof(f2969,plain,
    ( $false
    | spl10_9
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_66 ),
    inference(subsumption_resolution,[],[f2968,f2515])).

fof(f2515,plain,
    ( ~ v2_tops_2(sK1,sK2)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f2514])).

fof(f2514,plain,
    ( spl10_9
  <=> v2_tops_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f2968,plain,
    ( v2_tops_2(sK1,sK2)
    | ~ spl10_10
    | ~ spl10_22
    | ~ spl10_66 ),
    inference(subsumption_resolution,[],[f2966,f2520])).

fof(f2520,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f2519])).

fof(f2519,plain,
    ( spl10_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f2966,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v2_tops_2(sK1,sK2)
    | ~ spl10_22
    | ~ spl10_66 ),
    inference(resolution,[],[f2954,f2672])).

fof(f2672,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v2_tops_2(X0,sK2) )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f2671])).

fof(f2671,plain,
    ( spl10_22
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v2_tops_2(X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f2954,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f2953])).

fof(f2953,plain,
    ( spl10_66
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f2955,plain,
    ( spl10_66
    | ~ spl10_5
    | ~ spl10_7
    | spl10_9
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f2951,f2519,f2514,f2505,f2497,f2953])).

fof(f2497,plain,
    ( spl10_5
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f2505,plain,
    ( spl10_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f2951,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl10_5
    | ~ spl10_7
    | spl10_9
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f2949,f2515])).

fof(f2949,plain,
    ( v2_tops_2(sK1,sK2)
    | r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl10_5
    | ~ spl10_7
    | ~ spl10_10 ),
    inference(resolution,[],[f2946,f2520])).

fof(f2946,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v2_tops_2(X0,sK2)
        | r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl10_5
    | ~ spl10_7 ),
    inference(resolution,[],[f2868,f2498])).

fof(f2498,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f2497])).

fof(f2868,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_tops_2(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | r2_hidden(sK4(X1,X0),X0) )
    | ~ spl10_7 ),
    inference(resolution,[],[f2551,f2506])).

fof(f2506,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f2505])).

fof(f2551,plain,(
    ! [X4,X2,X3] :
      ( ~ l1_pre_topc(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v2_tops_2(X3,X2)
      | ~ m1_pre_topc(X2,X4)
      | r2_hidden(sK4(X2,X3),X3) ) ),
    inference(resolution,[],[f2451,f2472])).

fof(f2472,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2412])).

fof(f2412,plain,(
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

fof(f2451,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2421])).

fof(f2421,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2419,f2420])).

fof(f2420,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2419,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2418])).

fof(f2418,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2396])).

fof(f2396,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2395])).

fof(f2395,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2243])).

fof(f2243,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f2688,plain,
    ( ~ spl10_5
    | ~ spl10_7
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f2686])).

fof(f2686,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_7
    | spl10_21 ),
    inference(unit_resulting_resolution,[],[f2506,f2498,f2669,f2472])).

fof(f2669,plain,
    ( ~ l1_pre_topc(sK2)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f2668])).

fof(f2668,plain,
    ( spl10_21
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

% (9490)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f2673,plain,
    ( ~ spl10_21
    | spl10_22
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f2666,f2505,f2501,f2497,f2493,f2671,f2668])).

fof(f2493,plain,
    ( spl10_4
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f2501,plain,
    ( spl10_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f2666,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | v2_tops_2(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ l1_pre_topc(sK2) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f2662,f2452])).

fof(f2452,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2421])).

fof(f2662,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | v4_pre_topc(sK4(sK2,X0),sK2)
        | v2_tops_2(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ l1_pre_topc(sK2) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2659,f2450])).

fof(f2450,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2421])).

fof(f2659,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK2) )
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2652,f2498])).

fof(f2652,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X1,X0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(duplicate_literal_removal,[],[f2651])).

fof(f2651,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X1,X0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(condensation,[],[f2650])).

fof(f2650,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(X2,sK1)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ m1_pre_topc(X4,sK0)
        | v4_pre_topc(X2,X4) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2630,f2603])).

fof(f2603,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(X1,sK0)
        | v4_pre_topc(X0,X1) )
    | ~ spl10_7 ),
    inference(resolution,[],[f2602,f2506])).

fof(f2602,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | v4_pre_topc(X3,X2) ) ),
    inference(subsumption_resolution,[],[f2476,f2471])).

fof(f2471,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f2411])).

fof(f2411,plain,(
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

fof(f2476,plain,(
    ! [X2,X0,X3] :
      ( v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2460])).

fof(f2460,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2405])).

fof(f2405,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2404])).

fof(f2404,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2368])).

fof(f2368,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f2630,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2617,f2536])).

fof(f2536,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl10_7 ),
    inference(resolution,[],[f2471,f2506])).

fof(f2617,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f2614,f2494])).

% (9485)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
fof(f2494,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f2493])).

fof(f2614,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_2(sK1,sK0)
        | ~ r2_hidden(X0,sK1)
        | v4_pre_topc(X0,sK0) )
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(resolution,[],[f2607,f2502])).

fof(f2502,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f2501])).

fof(f2607,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tops_2(X1,sK0)
        | ~ r2_hidden(X0,X1)
        | v4_pre_topc(X0,sK0) )
    | ~ spl10_7 ),
    inference(resolution,[],[f2449,f2506])).

fof(f2449,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v4_pre_topc(X3,X0) ) ),
    inference(cnf_transformation,[],[f2421])).

fof(f2521,plain,
    ( spl10_10
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f2517,f2489,f2481,f2519])).

fof(f2481,plain,
    ( spl10_1
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f2489,plain,
    ( spl10_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f2517,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f2490,f2482])).

fof(f2482,plain,
    ( sK1 = sK3
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f2481])).

fof(f2490,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f2489])).

fof(f2516,plain,
    ( ~ spl10_9
    | ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f2512,f2485,f2481,f2514])).

fof(f2485,plain,
    ( spl10_2
  <=> v2_tops_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f2512,plain,
    ( ~ v2_tops_2(sK1,sK2)
    | ~ spl10_1
    | spl10_2 ),
    inference(forward_demodulation,[],[f2486,f2482])).

fof(f2486,plain,
    ( ~ v2_tops_2(sK3,sK2)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f2485])).

fof(f2507,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f2438,f2505])).

fof(f2438,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2417])).

fof(f2417,plain,
    ( ~ v2_tops_2(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & v2_tops_2(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2386,f2416,f2415,f2414,f2413])).

fof(f2413,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
                & v2_tops_2(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2414,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
            & v2_tops_2(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
          & v2_tops_2(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f2415,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tops_2(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
        & v2_tops_2(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v2_tops_2(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & v2_tops_2(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2416,plain,
    ( ? [X3] :
        ( ~ v2_tops_2(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ~ v2_tops_2(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f2386,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2385])).

fof(f2385,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v2_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2371])).

fof(f2371,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v2_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2370])).

fof(f2370,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v2_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v2_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_2)).

fof(f2503,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f2439,f2501])).

fof(f2439,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f2417])).

fof(f2499,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f2440,f2497])).

fof(f2440,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f2417])).

fof(f2495,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f2441,f2493])).

fof(f2441,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f2417])).

fof(f2491,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f2442,f2489])).

fof(f2442,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f2417])).

fof(f2487,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f2444,f2485])).

fof(f2444,plain,(
    ~ v2_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f2417])).

fof(f2483,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f2443,f2481])).

fof(f2443,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f2417])).
%------------------------------------------------------------------------------
