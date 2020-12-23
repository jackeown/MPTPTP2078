%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1523+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 339 expanded)
%              Number of leaves         :   33 ( 159 expanded)
%              Depth                    :   17
%              Number of atoms          :  629 (2615 expanded)
%              Number of equality atoms :  100 ( 538 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3515,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3037,f3041,f3048,f3056,f3057,f3069,f3073,f3077,f3081,f3085,f3095,f3133,f3144,f3157,f3165,f3198,f3240,f3326,f3496,f3497,f3501,f3514])).

fof(f3514,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f3513])).

fof(f3513,plain,
    ( $false
    | spl8_5
    | ~ spl8_6
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f3512,f3055])).

fof(f3055,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f3054])).

fof(f3054,plain,
    ( spl8_6
  <=> r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f3512,plain,
    ( ~ r2_orders_2(sK0,sK2,sK3)
    | spl8_5
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f3508,f3072])).

fof(f3072,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f3071])).

fof(f3071,plain,
    ( spl8_10
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f3508,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_orders_2(sK0,sK2,sK3)
    | spl8_5
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(resolution,[],[f3500,f3261])).

fof(f3261,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X0,sK3) )
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(resolution,[],[f3183,f3068])).

fof(f3068,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f3067])).

fof(f3067,plain,
    ( spl8_9
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f3183,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X6,X7)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r1_orders_2(sK0,X6,X7) )
    | ~ spl8_13 ),
    inference(resolution,[],[f3020,f3084])).

fof(f3084,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f3083])).

fof(f3083,plain,
    ( spl8_13
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f3020,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2999])).

fof(f2999,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f2998])).

fof(f2998,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2984])).

fof(f2984,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1864])).

fof(f1864,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f3500,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f3050])).

fof(f3050,plain,
    ( spl8_5
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f3501,plain,
    ( spl8_40
    | ~ spl8_5
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35
    | spl8_37 ),
    inference(avatar_split_clause,[],[f3499,f3272,f3238,f3196,f3083,f3079,f3071,f3067,f3050,f3295])).

fof(f3295,plain,
    ( spl8_40
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f3079,plain,
    ( spl8_12
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f3196,plain,
    ( spl8_30
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f3238,plain,
    ( spl8_35
  <=> u1_orders_2(sK0) = u1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f3272,plain,
    ( spl8_37
  <=> r2_orders_2(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f3499,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | sK2 = sK3
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35
    | spl8_37 ),
    inference(subsumption_resolution,[],[f3498,f3273])).

fof(f3273,plain,
    ( ~ r2_orders_2(sK1,sK2,sK3)
    | spl8_37 ),
    inference(avatar_component_clause,[],[f3272])).

fof(f3498,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | sK2 = sK3
    | r2_orders_2(sK1,sK2,sK3)
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f3479,f3072])).

fof(f3479,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | sK2 = sK3
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_orders_2(sK1,sK2,sK3)
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f3475,f3068])).

fof(f3475,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | sK2 = sK3
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_orders_2(sK1,sK2,sK3)
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(resolution,[],[f3324,f3303])).

fof(f3303,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK1,X0,sK3)
        | sK3 = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK1,X0,sK3) )
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_30 ),
    inference(resolution,[],[f3301,f3068])).

fof(f3301,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | X8 = X9
        | ~ r1_orders_2(sK1,X8,X9)
        | r2_orders_2(sK1,X8,X9) )
    | ~ spl8_12
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f3300,f3197])).

fof(f3197,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f3196])).

fof(f3300,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | X8 = X9
        | ~ r1_orders_2(sK1,X8,X9)
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_orders_2(sK1,X8,X9) )
    | ~ spl8_12
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f3191,f3197])).

fof(f3191,plain,
    ( ! [X8,X9] :
        ( X8 = X9
        | ~ r1_orders_2(sK1,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(sK1))
        | ~ m1_subset_1(X8,u1_struct_0(sK1))
        | r2_orders_2(sK1,X8,X9) )
    | ~ spl8_12 ),
    inference(resolution,[],[f3022,f3080])).

fof(f3080,plain,
    ( l1_orders_2(sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f3079])).

fof(f3022,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2999])).

fof(f3324,plain,
    ( ! [X1] :
        ( r1_orders_2(sK1,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X1) )
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(resolution,[],[f3320,f3072])).

fof(f3320,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X0)
        | ~ r1_orders_2(sK0,X1,X0) )
    | ~ spl8_12
    | ~ spl8_13
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f3319,f3084])).

fof(f3319,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_12
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(duplicate_literal_removal,[],[f3318])).

fof(f3318,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_12
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(resolution,[],[f3247,f3018])).

fof(f3018,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2997])).

fof(f2997,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2983])).

fof(f2983,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1885])).

fof(f1885,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f3247,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl8_12
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f3246,f3197])).

fof(f3246,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_12
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f3245,f3197])).

fof(f3245,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl8_12
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f3242,f3080])).

fof(f3242,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl8_35 ),
    inference(superposition,[],[f3019,f3239])).

fof(f3239,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f3238])).

fof(f3019,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2997])).

fof(f3497,plain,
    ( sK2 != sK3
    | r2_orders_2(sK0,sK2,sK2)
    | ~ r2_orders_2(sK0,sK2,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3496,plain,
    ( sK2 != sK4
    | sK3 != sK5
    | r2_orders_2(sK1,sK4,sK5)
    | ~ r2_orders_2(sK1,sK2,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3326,plain,
    ( ~ spl8_5
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(avatar_contradiction_clause,[],[f3322])).

fof(f3322,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_9
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f3051,f3094,f3068,f3072,f3320])).

fof(f3094,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f3093])).

fof(f3093,plain,
    ( spl8_15
  <=> r1_orders_2(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f3051,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f3050])).

fof(f3240,plain,
    ( spl8_35
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f3236,f3163,f3238])).

fof(f3163,plain,
    ( spl8_26
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f3236,plain,
    ( u1_orders_2(sK0) = u1_orders_2(sK1)
    | ~ spl8_26 ),
    inference(equality_resolution,[],[f3164])).

fof(f3164,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X1 )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f3163])).

fof(f3198,plain,
    ( spl8_30
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f3194,f3155,f3196])).

fof(f3155,plain,
    ( spl8_25
  <=> ! [X1,X0] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f3194,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl8_25 ),
    inference(equality_resolution,[],[f3156])).

fof(f3156,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0 )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f3155])).

fof(f3165,plain,
    ( ~ spl8_18
    | spl8_26
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f3159,f3075,f3163,f3108])).

fof(f3108,plain,
    ( spl8_18
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f3075,plain,
    ( spl8_11
  <=> g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f3159,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_orders_2(sK1) = X1
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) )
    | ~ spl8_11 ),
    inference(superposition,[],[f3025,f3076])).

fof(f3076,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f3075])).

fof(f3025,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f2985])).

fof(f2985,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1926])).

fof(f1926,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f3157,plain,
    ( ~ spl8_18
    | spl8_25
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f3151,f3075,f3155,f3108])).

fof(f3151,plain,
    ( ! [X0,X1] :
        ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X0
        | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) )
    | ~ spl8_11 ),
    inference(superposition,[],[f3024,f3076])).

fof(f3024,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f2985])).

fof(f3144,plain,
    ( ~ spl8_12
    | spl8_18 ),
    inference(avatar_contradiction_clause,[],[f3143])).

fof(f3143,plain,
    ( $false
    | ~ spl8_12
    | spl8_18 ),
    inference(subsumption_resolution,[],[f3141,f3080])).

fof(f3141,plain,
    ( ~ l1_orders_2(sK1)
    | spl8_18 ),
    inference(resolution,[],[f3029,f3109])).

fof(f3109,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f3108])).

fof(f3029,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2989])).

% (32180)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
fof(f2989,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f3133,plain,
    ( ~ spl8_22
    | ~ spl8_10
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f3124,f3083,f3071,f3131])).

fof(f3131,plain,
    ( spl8_22
  <=> r2_orders_2(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f3124,plain,
    ( ~ r2_orders_2(sK0,sK2,sK2)
    | ~ spl8_10
    | ~ spl8_13 ),
    inference(resolution,[],[f3120,f3072])).

fof(f3120,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X3,X3) )
    | ~ spl8_13 ),
    inference(resolution,[],[f3032,f3084])).

fof(f3032,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f3031])).

fof(f3031,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3021])).

fof(f3021,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2999])).

fof(f3095,plain,
    ( ~ spl8_15
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f3091,f3043,f3039,f3035,f3093])).

fof(f3035,plain,
    ( spl8_1
  <=> sK3 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f3039,plain,
    ( spl8_2
  <=> sK2 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f3043,plain,
    ( spl8_3
  <=> r1_orders_2(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f3091,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3)
    | ~ spl8_1
    | ~ spl8_2
    | spl8_3 ),
    inference(forward_demodulation,[],[f3090,f3040])).

fof(f3040,plain,
    ( sK2 = sK4
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f3039])).

fof(f3090,plain,
    ( ~ r1_orders_2(sK1,sK4,sK3)
    | ~ spl8_1
    | spl8_3 ),
    inference(forward_demodulation,[],[f3044,f3036])).

fof(f3036,plain,
    ( sK3 = sK5
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f3035])).

fof(f3044,plain,
    ( ~ r1_orders_2(sK1,sK4,sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f3043])).

fof(f3085,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f3004,f3083])).

fof(f3004,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2996])).

fof(f2996,plain,
    ( ( ( ~ r2_orders_2(sK1,sK4,sK5)
        & r2_orders_2(sK0,sK2,sK3) )
      | ( ~ r1_orders_2(sK1,sK4,sK5)
        & r1_orders_2(sK0,sK2,sK3) ) )
    & sK3 = sK5
    & sK2 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f2980,f2995,f2994,f2993,f2992,f2991,f2990])).

fof(f2990,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ( ~ r2_orders_2(X1,X4,X5)
                                & r2_orders_2(X0,X2,X3) )
                              | ( ~ r1_orders_2(X1,X4,X5)
                                & r1_orders_2(X0,X2,X3) ) )
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(sK0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(sK0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2991,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ( ~ r2_orders_2(X1,X4,X5)
                            & r2_orders_2(sK0,X2,X3) )
                          | ( ~ r1_orders_2(X1,X4,X5)
                            & r1_orders_2(sK0,X2,X3) ) )
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ( ~ r2_orders_2(sK1,X4,X5)
                          & r2_orders_2(sK0,X2,X3) )
                        | ( ~ r1_orders_2(sK1,X4,X5)
                          & r1_orders_2(sK0,X2,X3) ) )
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(sK1)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2992,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ( ~ r2_orders_2(sK1,X4,X5)
                        & r2_orders_2(sK0,X2,X3) )
                      | ( ~ r1_orders_2(sK1,X4,X5)
                        & r1_orders_2(sK0,X2,X3) ) )
                    & X3 = X5
                    & X2 = X4
                    & m1_subset_1(X5,u1_struct_0(sK1)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ( ~ r2_orders_2(sK1,X4,X5)
                      & r2_orders_2(sK0,sK2,X3) )
                    | ( ~ r1_orders_2(sK1,X4,X5)
                      & r1_orders_2(sK0,sK2,X3) ) )
                  & X3 = X5
                  & sK2 = X4
                  & m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2993,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ( ~ r2_orders_2(sK1,X4,X5)
                    & r2_orders_2(sK0,sK2,X3) )
                  | ( ~ r1_orders_2(sK1,X4,X5)
                    & r1_orders_2(sK0,sK2,X3) ) )
                & X3 = X5
                & sK2 = X4
                & m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ( ~ r2_orders_2(sK1,X4,X5)
                  & r2_orders_2(sK0,sK2,sK3) )
                | ( ~ r1_orders_2(sK1,X4,X5)
                  & r1_orders_2(sK0,sK2,sK3) ) )
              & sK3 = X5
              & sK2 = X4
              & m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2994,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ( ~ r2_orders_2(sK1,X4,X5)
                & r2_orders_2(sK0,sK2,sK3) )
              | ( ~ r1_orders_2(sK1,X4,X5)
                & r1_orders_2(sK0,sK2,sK3) ) )
            & sK3 = X5
            & sK2 = X4
            & m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ( ( ~ r2_orders_2(sK1,sK4,X5)
              & r2_orders_2(sK0,sK2,sK3) )
            | ( ~ r1_orders_2(sK1,sK4,X5)
              & r1_orders_2(sK0,sK2,sK3) ) )
          & sK3 = X5
          & sK2 = sK4
          & m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f2995,plain,
    ( ? [X5] :
        ( ( ( ~ r2_orders_2(sK1,sK4,X5)
            & r2_orders_2(sK0,sK2,sK3) )
          | ( ~ r1_orders_2(sK1,sK4,X5)
            & r1_orders_2(sK0,sK2,sK3) ) )
        & sK3 = X5
        & sK2 = sK4
        & m1_subset_1(X5,u1_struct_0(sK1)) )
   => ( ( ( ~ r2_orders_2(sK1,sK4,sK5)
          & r2_orders_2(sK0,sK2,sK3) )
        | ( ~ r1_orders_2(sK1,sK4,sK5)
          & r1_orders_2(sK0,sK2,sK3) ) )
      & sK3 = sK5
      & sK2 = sK4
      & m1_subset_1(sK5,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f2980,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f2979])).

fof(f2979,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2964])).

fof(f2964,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( ( X3 = X5
                                  & X2 = X4 )
                               => ( ( r2_orders_2(X0,X2,X3)
                                   => r2_orders_2(X1,X4,X5) )
                                  & ( r1_orders_2(X0,X2,X3)
                                   => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2963])).

fof(f2963,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_0)).

fof(f3081,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f3005,f3079])).

fof(f3005,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f2996])).

fof(f3077,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f3006,f3075])).

fof(f3006,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f2996])).

fof(f3073,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f3007,f3071])).

fof(f3007,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2996])).

fof(f3069,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f3008,f3067])).

fof(f3008,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2996])).

fof(f3057,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f3013,f3054,f3050])).

fof(f3013,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f2996])).

fof(f3056,plain,
    ( ~ spl8_3
    | spl8_6 ),
    inference(avatar_split_clause,[],[f3014,f3054,f3043])).

fof(f3014,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f2996])).

fof(f3048,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f3016,f3046,f3043])).

fof(f3046,plain,
    ( spl8_4
  <=> r2_orders_2(sK1,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f3016,plain,
    ( ~ r2_orders_2(sK1,sK4,sK5)
    | ~ r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f2996])).

fof(f3041,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f3011,f3039])).

fof(f3011,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f2996])).

fof(f3037,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f3012,f3035])).

fof(f3012,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f2996])).

% (32177)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
%------------------------------------------------------------------------------
