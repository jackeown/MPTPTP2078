%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1535+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 935 expanded)
%              Number of leaves         :   21 ( 296 expanded)
%              Depth                    :   22
%              Number of atoms          :  505 (5217 expanded)
%              Number of equality atoms :   72 ( 952 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3503,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3097,f3102,f3107,f3108,f3140,f3144,f3299,f3303,f3410,f3466,f3485,f3502])).

fof(f3502,plain,
    ( ~ spl9_7
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(avatar_contradiction_clause,[],[f3501])).

fof(f3501,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3500,f3401])).

fof(f3401,plain,
    ( m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f3400])).

fof(f3400,plain,
    ( spl9_27
  <=> m1_subset_1(sK2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f3500,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ spl9_7
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f3499,f3289])).

fof(f3289,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f3286])).

fof(f3286,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != k7_lattice3(k7_lattice3(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f3163,f3151])).

fof(f3151,plain,(
    g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = k7_lattice3(k7_lattice3(sK0)) ),
    inference(backward_demodulation,[],[f3046,f3112])).

fof(f3112,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = k7_lattice3(k7_lattice3(sK0)) ),
    inference(resolution,[],[f3044,f3078])).

fof(f3078,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    inference(cnf_transformation,[],[f3014])).

fof(f3014,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2961])).

fof(f2961,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = k7_lattice3(k7_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

fof(f3044,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3019])).

fof(f3019,plain,
    ( ( ( ~ v2_yellow_0(sK1)
        & v2_yellow_0(sK0) )
      | ( ~ v1_yellow_0(sK1)
        & v1_yellow_0(sK0) ) )
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2994,f3018,f3017])).

fof(f3017,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v2_yellow_0(X1)
                & v2_yellow_0(X0) )
              | ( ~ v1_yellow_0(X1)
                & v1_yellow_0(X0) ) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(sK0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(sK0) ) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3018,plain,
    ( ? [X1] :
        ( ( ( ~ v2_yellow_0(X1)
            & v2_yellow_0(sK0) )
          | ( ~ v1_yellow_0(X1)
            & v1_yellow_0(sK0) ) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ( ( ~ v2_yellow_0(sK1)
          & v2_yellow_0(sK0) )
        | ( ~ v1_yellow_0(sK1)
          & v1_yellow_0(sK0) ) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2994,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f2993])).

fof(f2993,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v2_yellow_0(X1)
              & v2_yellow_0(X0) )
            | ( ~ v1_yellow_0(X1)
              & v1_yellow_0(X0) ) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2969])).

fof(f2969,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ( ( v2_yellow_0(X0)
                 => v2_yellow_0(X1) )
                & ( v1_yellow_0(X0)
                 => v1_yellow_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2968])).

fof(f2968,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ( ( v2_yellow_0(X0)
               => v2_yellow_0(X1) )
              & ( v1_yellow_0(X0)
               => v1_yellow_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_0)).

fof(f3046,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f3019])).

fof(f3163,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != k7_lattice3(k7_lattice3(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(forward_demodulation,[],[f3154,f3112])).

fof(f3154,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK0) = X0 ) ),
    inference(resolution,[],[f3114,f3068])).

fof(f3068,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f3005])).

fof(f3005,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f3114,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f3044,f3081])).

fof(f3081,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f3016])).

fof(f3016,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f3499,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK1))
    | ~ spl9_7
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3498,f3112])).

fof(f3498,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK1))
    | ~ spl9_7
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f3497,f3289])).

fof(f3497,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK1))
    | ~ spl9_7
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f3496,f3348])).

fof(f3348,plain,(
    u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(trivial_inequality_removal,[],[f3345])).

fof(f3345,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != k7_lattice3(k7_lattice3(sK0))
    | u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(superposition,[],[f3164,f3309])).

fof(f3309,plain,(
    k7_lattice3(k7_lattice3(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    inference(backward_demodulation,[],[f3151,f3289])).

fof(f3164,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != k7_lattice3(k7_lattice3(sK0))
      | u1_orders_2(sK0) = X3 ) ),
    inference(forward_demodulation,[],[f3155,f3112])).

fof(f3155,plain,(
    ! [X2,X3] :
      ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(sK0) = X3 ) ),
    inference(resolution,[],[f3114,f3069])).

fof(f3069,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f3005])).

fof(f3496,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != k7_lattice3(k7_lattice3(sK0))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK1))
    | ~ spl9_7
    | ~ spl9_27
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3495,f3401])).

fof(f3495,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != k7_lattice3(k7_lattice3(sK0))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ spl9_7
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3492,f3045])).

fof(f3045,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f3019])).

fof(f3492,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != k7_lattice3(k7_lattice3(sK0))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ spl9_7
    | ~ spl9_28 ),
    inference(resolution,[],[f3405,f3480])).

fof(f3480,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f3479,f3289])).

fof(f3479,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f3139,f3289])).

fof(f3139,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f3138])).

fof(f3138,plain,
    ( spl9_7
  <=> ! [X0] :
        ( ~ r2_lattice3(sK1,u1_struct_0(sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f3405,plain,
    ( ! [X0] :
        ( r2_lattice3(X0,u1_struct_0(sK0),sK2(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(sK2(sK0),u1_struct_0(X0)) )
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f3404])).

fof(f3404,plain,
    ( spl9_28
  <=> ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK0))
        | r2_lattice3(X0,u1_struct_0(sK0),sK2(sK0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(sK2(sK0),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f3485,plain,
    ( ~ spl9_27
    | spl9_28
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f3484,f3104,f3404,f3400])).

fof(f3104,plain,
    ( spl9_4
  <=> v2_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f3484,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK0))
        | ~ m1_subset_1(sK2(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
        | ~ l1_orders_2(X0)
        | r2_lattice3(X0,u1_struct_0(sK0),sK2(sK0)) )
    | ~ spl9_4 ),
    inference(resolution,[],[f3482,f3304])).

fof(f3304,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_lattice3(sK0,X7,X8)
      | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X9),u1_orders_2(X9))
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ l1_orders_2(X9)
      | r2_lattice3(X9,X7,X8) ) ),
    inference(forward_demodulation,[],[f3116,f3112])).

fof(f3116,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_lattice3(sK0,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X9),u1_orders_2(X9))
      | ~ l1_orders_2(X9)
      | r2_lattice3(X9,X7,X8) ) ),
    inference(resolution,[],[f3044,f3084])).

fof(f3084,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | r2_lattice3(X1,X2,X4) ) ),
    inference(equality_resolution,[],[f3072])).

fof(f3072,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3008])).

fof(f3008,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3007])).

fof(f3007,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) )
                    & ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2971])).

fof(f2971,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f3482,plain,
    ( r2_lattice3(sK0,u1_struct_0(sK0),sK2(sK0))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3481,f3044])).

fof(f3481,plain,
    ( r2_lattice3(sK0,u1_struct_0(sK0),sK2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f3106,f3052])).

fof(f3052,plain,(
    ! [X0] :
      ( ~ v2_yellow_0(X0)
      | r2_lattice3(X0,u1_struct_0(X0),sK2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f3023,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r2_lattice3(X0,u1_struct_0(X0),sK2(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f3021,f3022])).

fof(f3022,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r2_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,u1_struct_0(X0),sK2(X0))
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3021,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r2_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3020])).

fof(f3020,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r2_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2995])).

fof(f2995,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2964])).

fof(f2964,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_0)).

fof(f3106,plain,
    ( v2_yellow_0(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f3104])).

fof(f3466,plain,
    ( ~ spl9_8
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(avatar_contradiction_clause,[],[f3465])).

fof(f3465,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f3464,f3294])).

fof(f3294,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f3293])).

fof(f3293,plain,
    ( spl9_21
  <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f3464,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl9_8
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f3463,f3289])).

fof(f3463,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK1))
    | ~ spl9_8
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f3462,f3112])).

fof(f3462,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != k7_lattice3(k7_lattice3(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK1))
    | ~ spl9_8
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f3461,f3289])).

fof(f3461,plain,
    ( k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK1))
    | ~ spl9_8
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(forward_demodulation,[],[f3460,f3348])).

fof(f3460,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != k7_lattice3(k7_lattice3(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK1))
    | ~ spl9_8
    | ~ spl9_21
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f3459,f3294])).

fof(f3459,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != k7_lattice3(k7_lattice3(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f3456,f3045])).

fof(f3456,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != k7_lattice3(k7_lattice3(sK0))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(resolution,[],[f3298,f3317])).

fof(f3317,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_8 ),
    inference(forward_demodulation,[],[f3307,f3289])).

fof(f3307,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl9_8 ),
    inference(backward_demodulation,[],[f3143,f3289])).

fof(f3143,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f3142])).

fof(f3142,plain,
    ( spl9_8
  <=> ! [X1] :
        ( ~ r1_lattice3(sK1,u1_struct_0(sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f3298,plain,
    ( ! [X0] :
        ( r1_lattice3(X0,u1_struct_0(sK0),sK3(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(sK3(sK0),u1_struct_0(X0)) )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f3297])).

fof(f3297,plain,
    ( spl9_22
  <=> ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK0))
        | r1_lattice3(X0,u1_struct_0(sK0),sK3(sK0))
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(sK3(sK0),u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f3410,plain,
    ( ~ spl9_4
    | spl9_27 ),
    inference(avatar_contradiction_clause,[],[f3409])).

fof(f3409,plain,
    ( $false
    | ~ spl9_4
    | spl9_27 ),
    inference(subsumption_resolution,[],[f3408,f3044])).

fof(f3408,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl9_4
    | spl9_27 ),
    inference(subsumption_resolution,[],[f3407,f3106])).

fof(f3407,plain,
    ( ~ v2_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_27 ),
    inference(resolution,[],[f3402,f3051])).

fof(f3051,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f3402,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | spl9_27 ),
    inference(avatar_component_clause,[],[f3400])).

fof(f3303,plain,
    ( ~ spl9_3
    | spl9_21 ),
    inference(avatar_contradiction_clause,[],[f3302])).

fof(f3302,plain,
    ( $false
    | ~ spl9_3
    | spl9_21 ),
    inference(subsumption_resolution,[],[f3301,f3044])).

fof(f3301,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl9_3
    | spl9_21 ),
    inference(subsumption_resolution,[],[f3300,f3101])).

fof(f3101,plain,
    ( v1_yellow_0(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f3099])).

fof(f3099,plain,
    ( spl9_3
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f3300,plain,
    ( ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | spl9_21 ),
    inference(resolution,[],[f3295,f3054])).

fof(f3054,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3027])).

fof(f3027,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r1_lattice3(X0,u1_struct_0(X0),sK3(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f3025,f3026])).

fof(f3026,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK3(X0))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3025,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r1_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f3024])).

fof(f3024,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r1_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f2996])).

fof(f2996,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2963])).

fof(f2963,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

fof(f3295,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | spl9_21 ),
    inference(avatar_component_clause,[],[f3293])).

fof(f3299,plain,
    ( ~ spl9_21
    | spl9_22
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f3291,f3099,f3297,f3293])).

fof(f3291,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != k7_lattice3(k7_lattice3(sK0))
        | ~ m1_subset_1(sK3(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
        | ~ l1_orders_2(X0)
        | r1_lattice3(X0,u1_struct_0(sK0),sK3(sK0)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f3284,f3148])).

fof(f3148,plain,
    ( r1_lattice3(sK0,u1_struct_0(sK0),sK3(sK0))
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f3147,f3044])).

fof(f3147,plain,
    ( r1_lattice3(sK0,u1_struct_0(sK0),sK3(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f3101,f3055])).

fof(f3055,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(X0)
      | r1_lattice3(X0,u1_struct_0(X0),sK3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3027])).

fof(f3284,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_lattice3(sK0,X4,X5)
      | k7_lattice3(k7_lattice3(sK0)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(X6)
      | r1_lattice3(X6,X4,X5) ) ),
    inference(forward_demodulation,[],[f3115,f3112])).

fof(f3115,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_lattice3(sK0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X6),u1_orders_2(X6))
      | ~ l1_orders_2(X6)
      | r1_lattice3(X6,X4,X5) ) ),
    inference(resolution,[],[f3044,f3083])).

fof(f3083,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | r1_lattice3(X1,X2,X4) ) ),
    inference(equality_resolution,[],[f3073])).

fof(f3073,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_lattice3(X1,X2,X4)
      | ~ r1_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3008])).

fof(f3144,plain,
    ( spl9_1
    | spl9_8 ),
    inference(avatar_split_clause,[],[f3128,f3142,f3090])).

fof(f3090,plain,
    ( spl9_1
  <=> v1_yellow_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f3128,plain,(
    ! [X1] :
      ( ~ r1_lattice3(sK1,u1_struct_0(sK1),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v1_yellow_0(sK1) ) ),
    inference(resolution,[],[f3045,f3056])).

fof(f3056,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f3027])).

fof(f3140,plain,
    ( spl9_2
    | spl9_7 ),
    inference(avatar_split_clause,[],[f3127,f3138,f3094])).

fof(f3094,plain,
    ( spl9_2
  <=> v2_yellow_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f3127,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK1,u1_struct_0(sK1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_yellow_0(sK1) ) ),
    inference(resolution,[],[f3045,f3053])).

fof(f3053,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f3023])).

fof(f3108,plain,
    ( spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f3047,f3104,f3099])).

fof(f3047,plain,
    ( v2_yellow_0(sK0)
    | v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f3019])).

fof(f3107,plain,
    ( ~ spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f3048,f3104,f3090])).

fof(f3048,plain,
    ( v2_yellow_0(sK0)
    | ~ v1_yellow_0(sK1) ),
    inference(cnf_transformation,[],[f3019])).

fof(f3102,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f3049,f3094,f3099])).

fof(f3049,plain,
    ( ~ v2_yellow_0(sK1)
    | v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f3019])).

fof(f3097,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f3050,f3094,f3090])).

fof(f3050,plain,
    ( ~ v2_yellow_0(sK1)
    | ~ v1_yellow_0(sK1) ),
    inference(cnf_transformation,[],[f3019])).
%------------------------------------------------------------------------------
