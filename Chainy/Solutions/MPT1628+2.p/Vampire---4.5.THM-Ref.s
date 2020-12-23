%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1628+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 10.88s
% Output     : Refutation 10.88s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 419 expanded)
%              Number of leaves         :   32 ( 204 expanded)
%              Depth                    :   10
%              Number of atoms          :  646 (2328 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3483,f3488,f3493,f3498,f3503,f3517,f3532,f3542,f3548,f3626,f14537,f14578,f14629,f15075,f15275,f15429,f15432,f15796,f16278,f16281])).

fof(f16281,plain,
    ( spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | ~ spl40_5
    | ~ spl40_7
    | ~ spl40_171
    | spl40_203
    | ~ spl40_215 ),
    inference(avatar_contradiction_clause,[],[f16280])).

fof(f16280,plain,
    ( $false
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | ~ spl40_5
    | ~ spl40_7
    | ~ spl40_171
    | spl40_203
    | ~ spl40_215 ),
    inference(subsumption_resolution,[],[f16279,f15810])).

fof(f15810,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2))),sK2)
    | ~ spl40_5
    | spl40_203 ),
    inference(unit_resulting_resolution,[],[f3502,f15795,f3368])).

fof(f3368,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3283])).

fof(f3283,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f3281,f3282])).

fof(f3282,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3281,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f3280])).

fof(f3280,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3194])).

fof(f3194,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f15795,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2))),sK3)
    | spl40_203 ),
    inference(avatar_component_clause,[],[f15793])).

fof(f15793,plain,
    ( spl40_203
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_203])])).

fof(f3502,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl40_5 ),
    inference(avatar_component_clause,[],[f3500])).

fof(f3500,plain,
    ( spl40_5
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_5])])).

fof(f16279,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2))),sK2)
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | ~ spl40_7
    | ~ spl40_171
    | ~ spl40_215 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f3512,f14577,f16277,f3351])).

fof(f3351,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ r1_waybel_0(X0,X1,X2)
      | ~ r1_orders_2(X1,sK7(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3274])).

fof(f3274,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
                      & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK7(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f3271,f3273,f3272])).

fof(f3272,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3273,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK7(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3271,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3270])).

fof(f3270,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3183])).

fof(f3183,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3182])).

fof(f3182,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3154])).

fof(f3154,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f16277,plain,
    ( r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2)))
    | ~ spl40_215 ),
    inference(avatar_component_clause,[],[f16275])).

fof(f16275,plain,
    ( spl40_215
  <=> r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_215])])).

fof(f14577,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl40_171 ),
    inference(avatar_component_clause,[],[f14575])).

fof(f14575,plain,
    ( spl40_171
  <=> m1_subset_1(sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_171])])).

fof(f3512,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl40_7 ),
    inference(avatar_component_clause,[],[f3510])).

fof(f3510,plain,
    ( spl40_7
  <=> r1_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_7])])).

fof(f3497,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl40_4 ),
    inference(avatar_component_clause,[],[f3495])).

fof(f3495,plain,
    ( spl40_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_4])])).

fof(f3492,plain,
    ( ~ v2_struct_0(sK1)
    | spl40_3 ),
    inference(avatar_component_clause,[],[f3490])).

fof(f3490,plain,
    ( spl40_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_3])])).

fof(f3487,plain,
    ( l1_struct_0(sK0)
    | ~ spl40_2 ),
    inference(avatar_component_clause,[],[f3485])).

fof(f3485,plain,
    ( spl40_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_2])])).

fof(f3482,plain,
    ( ~ v2_struct_0(sK0)
    | spl40_1 ),
    inference(avatar_component_clause,[],[f3480])).

fof(f3480,plain,
    ( spl40_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_1])])).

fof(f16278,plain,
    ( spl40_215
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_11
    | ~ spl40_106 ),
    inference(avatar_split_clause,[],[f15456,f7822,f3529,f3495,f3490,f3485,f3480,f16275])).

fof(f3529,plain,
    ( spl40_11
  <=> r1_waybel_0(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_11])])).

fof(f7822,plain,
    ( spl40_106
  <=> m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_106])])).

fof(f15456,plain,
    ( r1_orders_2(sK1,sK7(sK0,sK1,sK2),sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2)))
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_11
    | ~ spl40_106 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f7824,f3531,f3353])).

fof(f3353,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3274])).

fof(f3531,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK3)
    | spl40_11 ),
    inference(avatar_component_clause,[],[f3529])).

fof(f7824,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl40_106 ),
    inference(avatar_component_clause,[],[f7822])).

fof(f15796,plain,
    ( ~ spl40_203
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_11
    | ~ spl40_106 ),
    inference(avatar_split_clause,[],[f15443,f7822,f3529,f3495,f3490,f3485,f3480,f15793])).

fof(f15443,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2))),sK3)
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_11
    | ~ spl40_106 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f7824,f3531,f3354])).

fof(f3354,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK6(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3274])).

fof(f15432,plain,
    ( spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_13
    | ~ spl40_23
    | ~ spl40_183
    | ~ spl40_187
    | ~ spl40_193 ),
    inference(avatar_contradiction_clause,[],[f15431])).

fof(f15431,plain,
    ( $false
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_13
    | ~ spl40_23
    | ~ spl40_183
    | ~ spl40_187
    | ~ spl40_193 ),
    inference(subsumption_resolution,[],[f15430,f15293])).

fof(f15293,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3))),sK3)
    | ~ spl40_23
    | ~ spl40_187 ),
    inference(unit_resulting_resolution,[],[f3625,f15274,f3405])).

fof(f3405,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3223])).

fof(f3223,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f488])).

fof(f488,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f15274,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3))),sK2)
    | ~ spl40_187 ),
    inference(avatar_component_clause,[],[f15272])).

fof(f15272,plain,
    ( spl40_187
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_187])])).

fof(f3625,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ spl40_23 ),
    inference(avatar_component_clause,[],[f3623])).

fof(f3623,plain,
    ( spl40_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_23])])).

fof(f15430,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3))),sK3)
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_13
    | ~ spl40_183
    | ~ spl40_193 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f3541,f15074,f15428,f3349])).

fof(f3349,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
      | r2_waybel_0(X0,X1,X2)
      | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3269])).

fof(f3269,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5))
                      & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f3266,f3268,f3267])).

fof(f3267,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK4(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3268,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK5(X0,X1,X2,X5))
        & m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3266,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f3265])).

fof(f3265,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3181])).

fof(f3181,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3180])).

fof(f3180,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3155])).

fof(f3155,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f15428,plain,
    ( r1_orders_2(sK1,sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3)))
    | ~ spl40_193 ),
    inference(avatar_component_clause,[],[f15426])).

fof(f15426,plain,
    ( spl40_193
  <=> r1_orders_2(sK1,sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_193])])).

fof(f15074,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl40_183 ),
    inference(avatar_component_clause,[],[f15072])).

fof(f15072,plain,
    ( spl40_183
  <=> m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_183])])).

fof(f3541,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK3)
    | spl40_13 ),
    inference(avatar_component_clause,[],[f3539])).

fof(f3539,plain,
    ( spl40_13
  <=> r2_waybel_0(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_13])])).

fof(f15429,plain,
    ( spl40_193
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | ~ spl40_8
    | ~ spl40_35 ),
    inference(avatar_split_clause,[],[f14982,f3839,f3514,f3495,f3490,f3485,f3480,f15426])).

fof(f3514,plain,
    ( spl40_8
  <=> r2_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_8])])).

fof(f3839,plain,
    ( spl40_35
  <=> m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl40_35])])).

fof(f14982,plain,
    ( r1_orders_2(sK1,sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3)))
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | ~ spl40_8
    | ~ spl40_35 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f3841,f3516,f3346])).

fof(f3346,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X1,X5,sK5(X0,X1,X2,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3269])).

fof(f3516,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | ~ spl40_8 ),
    inference(avatar_component_clause,[],[f3514])).

fof(f3841,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl40_35 ),
    inference(avatar_component_clause,[],[f3839])).

fof(f15275,plain,
    ( spl40_187
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | ~ spl40_8
    | ~ spl40_35 ),
    inference(avatar_split_clause,[],[f14973,f3839,f3514,f3495,f3490,f3485,f3480,f15272])).

fof(f14973,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3))),sK2)
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | ~ spl40_8
    | ~ spl40_35 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f3841,f3516,f3347])).

fof(f3347,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK5(X0,X1,X2,X5)),X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3269])).

fof(f15075,plain,
    ( spl40_183
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | ~ spl40_8
    | ~ spl40_35 ),
    inference(avatar_split_clause,[],[f14991,f3839,f3514,f3495,f3490,f3485,f3480,f15072])).

fof(f14991,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2,sK4(sK0,sK1,sK3)),u1_struct_0(sK1))
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | ~ spl40_8
    | ~ spl40_35 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f3841,f3516,f3345])).

fof(f3345,plain,(
    ! [X2,X0,X5,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X5),u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3269])).

fof(f14629,plain,
    ( ~ spl40_7
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_106 ),
    inference(avatar_split_clause,[],[f13325,f7822,f3495,f3490,f3485,f3480,f3510])).

fof(f13325,plain,
    ( ~ r1_waybel_0(sK0,sK1,sK2)
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_106 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f7823,f3350])).

fof(f3350,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3274])).

fof(f7823,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK1))
    | spl40_106 ),
    inference(avatar_component_clause,[],[f7822])).

fof(f14578,plain,
    ( spl40_171
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_11
    | ~ spl40_106 ),
    inference(avatar_split_clause,[],[f13400,f7822,f3529,f3495,f3490,f3485,f3480,f14575])).

fof(f13400,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3,sK7(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_11
    | ~ spl40_106 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f3531,f7824,f3352])).

fof(f3352,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3274])).

fof(f14537,plain,
    ( spl40_13
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_35 ),
    inference(avatar_split_clause,[],[f7815,f3839,f3495,f3490,f3485,f3480,f3539])).

fof(f7815,plain,
    ( r2_waybel_0(sK0,sK1,sK3)
    | spl40_1
    | ~ spl40_2
    | spl40_3
    | ~ spl40_4
    | spl40_35 ),
    inference(unit_resulting_resolution,[],[f3482,f3487,f3492,f3497,f3840,f3348])).

fof(f3348,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3269])).

fof(f3840,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK1))
    | spl40_35 ),
    inference(avatar_component_clause,[],[f3839])).

fof(f3626,plain,
    ( spl40_23
    | ~ spl40_5 ),
    inference(avatar_split_clause,[],[f3563,f3500,f3623])).

fof(f3563,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ spl40_5 ),
    inference(unit_resulting_resolution,[],[f3502,f3363])).

fof(f3363,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3275])).

fof(f3275,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f3548,plain,
    ( ~ spl40_11
    | ~ spl40_13 ),
    inference(avatar_split_clause,[],[f3344,f3539,f3529])).

fof(f3344,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK3)
    | ~ r1_waybel_0(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3264,plain,
    ( ( ( ~ r2_waybel_0(sK0,sK1,sK3)
        & r2_waybel_0(sK0,sK1,sK2) )
      | ( ~ r1_waybel_0(sK0,sK1,sK3)
        & r1_waybel_0(sK0,sK1,sK2) ) )
    & r1_tarski(sK2,sK3)
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3179,f3263,f3262,f3261])).

fof(f3261,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ( ( ~ r2_waybel_0(X0,X1,X3)
                    & r2_waybel_0(X0,X1,X2) )
                  | ( ~ r1_waybel_0(X0,X1,X3)
                    & r1_waybel_0(X0,X1,X2) ) )
                & r1_tarski(X2,X3) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ( ( ~ r2_waybel_0(sK0,X1,X3)
                  & r2_waybel_0(sK0,X1,X2) )
                | ( ~ r1_waybel_0(sK0,X1,X3)
                  & r1_waybel_0(sK0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3262,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ( ( ~ r2_waybel_0(sK0,X1,X3)
                & r2_waybel_0(sK0,X1,X2) )
              | ( ~ r1_waybel_0(sK0,X1,X3)
                & r1_waybel_0(sK0,X1,X2) ) )
            & r1_tarski(X2,X3) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X3,X2] :
          ( ( ( ~ r2_waybel_0(sK0,sK1,X3)
              & r2_waybel_0(sK0,sK1,X2) )
            | ( ~ r1_waybel_0(sK0,sK1,X3)
              & r1_waybel_0(sK0,sK1,X2) ) )
          & r1_tarski(X2,X3) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3263,plain,
    ( ? [X3,X2] :
        ( ( ( ~ r2_waybel_0(sK0,sK1,X3)
            & r2_waybel_0(sK0,sK1,X2) )
          | ( ~ r1_waybel_0(sK0,sK1,X3)
            & r1_waybel_0(sK0,sK1,X2) ) )
        & r1_tarski(X2,X3) )
   => ( ( ( ~ r2_waybel_0(sK0,sK1,sK3)
          & r2_waybel_0(sK0,sK1,sK2) )
        | ( ~ r1_waybel_0(sK0,sK1,sK3)
          & r1_waybel_0(sK0,sK1,sK2) ) )
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3179,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3178])).

fof(f3178,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ( ( ~ r2_waybel_0(X0,X1,X3)
                  & r2_waybel_0(X0,X1,X2) )
                | ( ~ r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) )
              & r1_tarski(X2,X3) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3177])).

fof(f3177,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ( r1_tarski(X2,X3)
               => ( ( r2_waybel_0(X0,X1,X2)
                   => r2_waybel_0(X0,X1,X3) )
                  & ( r1_waybel_0(X0,X1,X2)
                   => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3176])).

fof(f3176,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

fof(f3542,plain,
    ( spl40_7
    | ~ spl40_13 ),
    inference(avatar_split_clause,[],[f3343,f3539,f3510])).

fof(f3343,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK3)
    | r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3532,plain,
    ( ~ spl40_11
    | spl40_8 ),
    inference(avatar_split_clause,[],[f3342,f3514,f3529])).

fof(f3342,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | ~ r1_waybel_0(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3517,plain,
    ( spl40_7
    | spl40_8 ),
    inference(avatar_split_clause,[],[f3341,f3514,f3510])).

fof(f3341,plain,
    ( r2_waybel_0(sK0,sK1,sK2)
    | r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3503,plain,(
    spl40_5 ),
    inference(avatar_split_clause,[],[f3340,f3500])).

fof(f3340,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3498,plain,(
    spl40_4 ),
    inference(avatar_split_clause,[],[f3339,f3495])).

fof(f3339,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3493,plain,(
    ~ spl40_3 ),
    inference(avatar_split_clause,[],[f3338,f3490])).

fof(f3338,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3488,plain,(
    spl40_2 ),
    inference(avatar_split_clause,[],[f3337,f3485])).

fof(f3337,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3264])).

fof(f3483,plain,(
    ~ spl40_1 ),
    inference(avatar_split_clause,[],[f3336,f3480])).

fof(f3336,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3264])).
%------------------------------------------------------------------------------
