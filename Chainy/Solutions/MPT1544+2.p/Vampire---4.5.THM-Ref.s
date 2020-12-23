%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1544+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 10.46s
% Output     : Refutation 10.46s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 590 expanded)
%              Number of leaves         :   17 ( 134 expanded)
%              Depth                    :   26
%              Number of atoms          : 1046 (5105 expanded)
%              Number of equality atoms :   85 ( 414 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5826,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4604,f4609,f4614,f4619,f4624,f4629,f4633,f5533,f5557,f5616,f5690,f5750,f5759,f5769,f5809,f5825])).

fof(f5825,plain,
    ( spl180_3
    | ~ spl180_28 ),
    inference(avatar_contradiction_clause,[],[f5824])).

fof(f5824,plain,
    ( $false
    | spl180_3
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f4607,f5823])).

fof(f5823,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5822,f4635])).

fof(f4635,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4634,f3440])).

fof(f3440,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3026])).

fof(f3026,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f3025])).

fof(f3025,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2986])).

fof(f2986,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( k13_lattice3(X0,X1,X2) = X3
                    <=> ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2985])).

fof(f2985,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

fof(f4634,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f3439,f3491])).

fof(f3491,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3049])).

fof(f3049,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3048])).

fof(f3048,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2806])).

fof(f2806,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f3439,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f3026])).

fof(f5822,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | v2_struct_0(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5821,f3435])).

fof(f3435,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3026])).

fof(f5821,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5820,f3437])).

fof(f3437,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3026])).

fof(f5820,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5819,f3436])).

fof(f3436,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3026])).

fof(f5819,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5818,f3440])).

fof(f5818,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5817,f3439])).

fof(f5817,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5782,f3438])).

fof(f3438,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3026])).

fof(f5782,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl180_28 ),
    inference(superposition,[],[f4476,f5528])).

fof(f5528,plain,
    ( sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ spl180_28 ),
    inference(avatar_component_clause,[],[f5526])).

fof(f5526,plain,
    ( spl180_28
  <=> sK3 = k10_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_28])])).

fof(f4476,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3819])).

fof(f3819,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f3121])).

fof(f3121,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3120])).

fof(f3120,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2892])).

fof(f2892,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

fof(f4607,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | spl180_3 ),
    inference(avatar_component_clause,[],[f4606])).

fof(f4606,plain,
    ( spl180_3
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_3])])).

fof(f5809,plain,
    ( spl180_2
    | ~ spl180_28 ),
    inference(avatar_contradiction_clause,[],[f5808])).

fof(f5808,plain,
    ( $false
    | spl180_2
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5807,f4635])).

fof(f5807,plain,
    ( v2_struct_0(sK0)
    | spl180_2
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5806,f3435])).

fof(f5806,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl180_2
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5805,f3437])).

fof(f5805,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl180_2
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5804,f3436])).

fof(f5804,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl180_2
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5803,f3440])).

fof(f5803,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl180_2
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5802,f3439])).

fof(f5802,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl180_2
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5801,f3438])).

fof(f5801,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl180_2
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5783,f4602])).

fof(f4602,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | spl180_2 ),
    inference(avatar_component_clause,[],[f4601])).

fof(f4601,plain,
    ( spl180_2
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_2])])).

fof(f5783,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ v5_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl180_28 ),
    inference(superposition,[],[f4477,f5528])).

fof(f4477,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3818])).

fof(f3818,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f3121])).

fof(f5769,plain,
    ( ~ spl180_1
    | spl180_27 ),
    inference(avatar_contradiction_clause,[],[f5768])).

fof(f5768,plain,
    ( $false
    | ~ spl180_1
    | spl180_27 ),
    inference(subsumption_resolution,[],[f5767,f3438])).

fof(f5767,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl180_1
    | spl180_27 ),
    inference(subsumption_resolution,[],[f5766,f3436])).

fof(f5766,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_1
    | spl180_27 ),
    inference(subsumption_resolution,[],[f5765,f3437])).

fof(f5765,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_1
    | spl180_27 ),
    inference(subsumption_resolution,[],[f5764,f3440])).

fof(f5764,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_1
    | spl180_27 ),
    inference(subsumption_resolution,[],[f5763,f3439])).

fof(f5763,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_1
    | spl180_27 ),
    inference(subsumption_resolution,[],[f5762,f4599])).

fof(f4599,plain,
    ( sK3 = k13_lattice3(sK0,sK1,sK2)
    | ~ spl180_1 ),
    inference(avatar_component_clause,[],[f4597])).

fof(f4597,plain,
    ( spl180_1
  <=> sK3 = k13_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_1])])).

fof(f5762,plain,
    ( sK3 != k13_lattice3(sK0,sK1,sK2)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl180_27 ),
    inference(superposition,[],[f5037,f3446])).

fof(f3446,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f3035,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3034])).

fof(f3034,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2897])).

fof(f2897,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f5037,plain,
    ( sK3 != k10_lattice3(sK0,sK1,sK2)
    | spl180_27 ),
    inference(avatar_component_clause,[],[f5036])).

fof(f5036,plain,
    ( spl180_27
  <=> sK3 = k10_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_27])])).

fof(f5759,plain,
    ( ~ spl180_2
    | ~ spl180_3
    | spl180_28
    | spl180_29 ),
    inference(avatar_contradiction_clause,[],[f5758])).

fof(f5758,plain,
    ( $false
    | ~ spl180_2
    | ~ spl180_3
    | spl180_28
    | spl180_29 ),
    inference(subsumption_resolution,[],[f5527,f5757])).

fof(f5757,plain,
    ( sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ spl180_2
    | ~ spl180_3
    | spl180_29 ),
    inference(subsumption_resolution,[],[f5756,f3438])).

fof(f5756,plain,
    ( ~ v5_orders_2(sK0)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ spl180_2
    | ~ spl180_3
    | spl180_29 ),
    inference(subsumption_resolution,[],[f5755,f4608])).

fof(f4608,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl180_3 ),
    inference(avatar_component_clause,[],[f4606])).

fof(f5755,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ v5_orders_2(sK0)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ spl180_2
    | spl180_29 ),
    inference(subsumption_resolution,[],[f5754,f4603])).

fof(f4603,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl180_2 ),
    inference(avatar_component_clause,[],[f4601])).

fof(f5754,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ v5_orders_2(sK0)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | spl180_29 ),
    inference(subsumption_resolution,[],[f5753,f3435])).

fof(f5753,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ v5_orders_2(sK0)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | spl180_29 ),
    inference(subsumption_resolution,[],[f5752,f3437])).

fof(f5752,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ v5_orders_2(sK0)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | spl180_29 ),
    inference(subsumption_resolution,[],[f5751,f3436])).

fof(f5751,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ v5_orders_2(sK0)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | spl180_29 ),
    inference(subsumption_resolution,[],[f5647,f3440])).

fof(f5647,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ v5_orders_2(sK0)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | spl180_29 ),
    inference(resolution,[],[f5532,f3805])).

fof(f3805,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK78(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f3115])).

fof(f3115,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3114])).

fof(f3114,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2999])).

fof(f2999,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X5)
                                & r1_orders_2(X0,X1,X5) )
                             => r1_orders_2(X0,X3,X5) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f2980])).

fof(f2980,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_0)).

fof(f5532,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | spl180_29 ),
    inference(avatar_component_clause,[],[f5530])).

fof(f5530,plain,
    ( spl180_29
  <=> m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_29])])).

fof(f5527,plain,
    ( sK3 != k10_lattice3(sK0,sK2,sK1)
    | spl180_28 ),
    inference(avatar_component_clause,[],[f5526])).

fof(f5750,plain,
    ( spl180_27
    | ~ spl180_28 ),
    inference(avatar_contradiction_clause,[],[f5749])).

fof(f5749,plain,
    ( $false
    | spl180_27
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5037,f5748])).

fof(f5748,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5747,f3438])).

fof(f5747,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5746,f3436])).

fof(f5746,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5745,f3437])).

fof(f5745,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5744,f3440])).

fof(f5744,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_28 ),
    inference(subsumption_resolution,[],[f5629,f3439])).

fof(f5629,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_28 ),
    inference(superposition,[],[f3812,f5528])).

fof(f3812,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3119])).

fof(f3119,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3118])).

fof(f3118,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2907])).

fof(f2907,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).

fof(f5690,plain,
    ( spl180_4
    | ~ spl180_5
    | ~ spl180_6
    | ~ spl180_7
    | ~ spl180_27 ),
    inference(avatar_contradiction_clause,[],[f5689])).

fof(f5689,plain,
    ( $false
    | spl180_4
    | ~ spl180_5
    | ~ spl180_6
    | ~ spl180_7
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5688,f4618])).

fof(f4618,plain,
    ( r1_orders_2(sK0,sK2,sK4)
    | ~ spl180_5 ),
    inference(avatar_component_clause,[],[f4616])).

fof(f4616,plain,
    ( spl180_5
  <=> r1_orders_2(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_5])])).

fof(f5688,plain,
    ( ~ r1_orders_2(sK0,sK2,sK4)
    | spl180_4
    | ~ spl180_6
    | ~ spl180_7
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5687,f4623])).

fof(f4623,plain,
    ( r1_orders_2(sK0,sK1,sK4)
    | ~ spl180_6 ),
    inference(avatar_component_clause,[],[f4621])).

fof(f4621,plain,
    ( spl180_6
  <=> r1_orders_2(sK0,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_6])])).

fof(f5687,plain,
    ( ~ r1_orders_2(sK0,sK1,sK4)
    | ~ r1_orders_2(sK0,sK2,sK4)
    | spl180_4
    | ~ spl180_7
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5670,f4628])).

fof(f4628,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl180_7 ),
    inference(avatar_component_clause,[],[f4626])).

fof(f4626,plain,
    ( spl180_7
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_7])])).

fof(f5670,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK4)
    | ~ r1_orders_2(sK0,sK2,sK4)
    | spl180_4
    | ~ spl180_27 ),
    inference(resolution,[],[f5593,f4613])).

fof(f4613,plain,
    ( ~ r1_orders_2(sK0,sK3,sK4)
    | spl180_4 ),
    inference(avatar_component_clause,[],[f4611])).

fof(f4611,plain,
    ( spl180_4
  <=> r1_orders_2(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_4])])).

fof(f5593,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2) )
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5592,f4635])).

fof(f5592,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2)
        | v2_struct_0(sK0) )
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5591,f3435])).

fof(f5591,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK3,X2)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2)
        | v2_struct_0(sK0) )
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5590,f3436])).

fof(f5590,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK3,X2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2)
        | v2_struct_0(sK0) )
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5589,f3437])).

fof(f5589,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK3,X2)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2)
        | v2_struct_0(sK0) )
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5588,f3440])).

fof(f5588,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK3,X2)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2)
        | v2_struct_0(sK0) )
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5587,f3439])).

fof(f5587,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK3,X2)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2)
        | v2_struct_0(sK0) )
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5543,f3438])).

fof(f5543,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK3,X2)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X2)
        | ~ r1_orders_2(sK0,sK2,X2)
        | v2_struct_0(sK0) )
    | ~ spl180_27 ),
    inference(superposition,[],[f4478,f5038])).

fof(f5038,plain,
    ( sK3 = k10_lattice3(sK0,sK1,sK2)
    | ~ spl180_27 ),
    inference(avatar_component_clause,[],[f5036])).

fof(f4478,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X4)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3817])).

fof(f3817,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | r1_orders_2(X0,X3,X4)
      | k10_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f3121])).

fof(f5616,plain,
    ( ~ spl180_27
    | spl180_28 ),
    inference(avatar_contradiction_clause,[],[f5615])).

fof(f5615,plain,
    ( $false
    | ~ spl180_27
    | spl180_28 ),
    inference(subsumption_resolution,[],[f5614,f3438])).

fof(f5614,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl180_27
    | spl180_28 ),
    inference(subsumption_resolution,[],[f5613,f3437])).

fof(f5613,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_27
    | spl180_28 ),
    inference(subsumption_resolution,[],[f5612,f3436])).

fof(f5612,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_27
    | spl180_28 ),
    inference(subsumption_resolution,[],[f5611,f3440])).

fof(f5611,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_27
    | spl180_28 ),
    inference(subsumption_resolution,[],[f5610,f3439])).

fof(f5610,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_27
    | spl180_28 ),
    inference(subsumption_resolution,[],[f5601,f5038])).

fof(f5601,plain,
    ( sK3 != k10_lattice3(sK0,sK1,sK2)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl180_28 ),
    inference(superposition,[],[f5527,f3812])).

fof(f5557,plain,
    ( spl180_1
    | ~ spl180_27 ),
    inference(avatar_contradiction_clause,[],[f5556])).

fof(f5556,plain,
    ( $false
    | spl180_1
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5555,f3438])).

fof(f5555,plain,
    ( ~ v5_orders_2(sK0)
    | spl180_1
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5554,f3436])).

fof(f5554,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl180_1
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5553,f3437])).

fof(f5553,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl180_1
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5552,f3440])).

fof(f5552,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl180_1
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5551,f3439])).

fof(f5551,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl180_1
    | ~ spl180_27 ),
    inference(subsumption_resolution,[],[f5535,f4598])).

fof(f4598,plain,
    ( sK3 != k13_lattice3(sK0,sK1,sK2)
    | spl180_1 ),
    inference(avatar_component_clause,[],[f4597])).

fof(f5535,plain,
    ( sK3 = k13_lattice3(sK0,sK1,sK2)
    | ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl180_27 ),
    inference(superposition,[],[f3446,f5038])).

fof(f5533,plain,
    ( spl180_28
    | ~ spl180_29
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_8 ),
    inference(avatar_split_clause,[],[f5524,f4631,f4606,f4601,f5530,f5526])).

fof(f4631,plain,
    ( spl180_8
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X4)
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r1_orders_2(sK0,sK1,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl180_8])])).

fof(f5524,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5523,f3438])).

fof(f5523,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0)
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5522,f4603])).

fof(f5522,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ v5_orders_2(sK0)
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5521,f3435])).

fof(f5521,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ v5_orders_2(sK0)
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5520,f3436])).

fof(f5520,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ v5_orders_2(sK0)
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5519,f3440])).

fof(f5519,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ v5_orders_2(sK0)
    | ~ spl180_2
    | ~ spl180_3
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5518,f4608])).

fof(f5518,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ v5_orders_2(sK0)
    | ~ spl180_2
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5508,f3437])).

fof(f5508,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ v5_orders_2(sK0)
    | ~ spl180_2
    | ~ spl180_8 ),
    inference(duplicate_literal_removal,[],[f5505])).

fof(f5505,plain,
    ( ~ m1_subset_1(sK78(sK0,sK2,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ v5_orders_2(sK0)
    | sK3 = k10_lattice3(sK0,sK2,sK1)
    | ~ spl180_2
    | ~ spl180_8 ),
    inference(resolution,[],[f5005,f3807])).

fof(f3807,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK78(X0,X1,X2,X3))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f3115])).

fof(f5005,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,sK1,sK78(sK0,sK2,X3,sK3))
        | ~ m1_subset_1(sK78(sK0,sK2,X3,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK3)
        | sK3 = k10_lattice3(sK0,sK2,X3) )
    | ~ spl180_2
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5004,f3438])).

fof(f5004,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK78(sK0,sK2,X3,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,sK2,X3,sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK3)
        | sK3 = k10_lattice3(sK0,sK2,X3)
        | ~ v5_orders_2(sK0) )
    | ~ spl180_2
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5003,f3435])).

fof(f5003,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK78(sK0,sK2,X3,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,sK2,X3,sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK3)
        | sK3 = k10_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0) )
    | ~ spl180_2
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5002,f3440])).

fof(f5002,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK78(sK0,sK2,X3,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,sK2,X3,sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK3)
        | sK3 = k10_lattice3(sK0,sK2,X3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0) )
    | ~ spl180_2
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f5001,f4603])).

fof(f5001,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK78(sK0,sK2,X3,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,sK2,X3,sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,X3,sK3)
        | sK3 = k10_lattice3(sK0,sK2,X3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0) )
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f4992,f3436])).

fof(f4992,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK78(sK0,sK2,X3,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,sK2,X3,sK3))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,X3,sK3)
        | sK3 = k10_lattice3(sK0,sK2,X3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0) )
    | ~ spl180_8 ),
    inference(duplicate_literal_removal,[],[f4989])).

fof(f4989,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK78(sK0,sK2,X3,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,sK2,X3,sK3))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,X3,sK3)
        | sK3 = k10_lattice3(sK0,sK2,X3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ r1_orders_2(sK0,X3,sK3)
        | ~ v5_orders_2(sK0)
        | sK3 = k10_lattice3(sK0,sK2,X3) )
    | ~ spl180_8 ),
    inference(resolution,[],[f4722,f3806])).

fof(f3806,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK78(X0,X1,X2,X3))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f3115])).

fof(f4722,plain,
    ( ! [X4,X3] :
        ( ~ r1_orders_2(sK0,sK2,sK78(sK0,X3,X4,sK3))
        | ~ m1_subset_1(sK78(sK0,X3,X4,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,X3,X4,sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK3)
        | ~ r1_orders_2(sK0,X4,sK3)
        | sK3 = k10_lattice3(sK0,X3,X4) )
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f4721,f3438])).

fof(f4721,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK78(sK0,X3,X4,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK78(sK0,X3,X4,sK3))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,X3,X4,sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK3)
        | ~ r1_orders_2(sK0,X4,sK3)
        | ~ v5_orders_2(sK0)
        | sK3 = k10_lattice3(sK0,X3,X4) )
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f4720,f3435])).

fof(f4720,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK78(sK0,X3,X4,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK78(sK0,X3,X4,sK3))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,X3,X4,sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK3)
        | ~ r1_orders_2(sK0,X4,sK3)
        | ~ v5_orders_2(sK0)
        | sK3 = k10_lattice3(sK0,X3,X4) )
    | ~ spl180_8 ),
    inference(subsumption_resolution,[],[f4701,f3440])).

fof(f4701,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK78(sK0,X3,X4,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,sK78(sK0,X3,X4,sK3))
        | ~ r1_orders_2(sK0,sK1,sK78(sK0,X3,X4,sK3))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,sK3)
        | ~ r1_orders_2(sK0,X4,sK3)
        | ~ v5_orders_2(sK0)
        | sK3 = k10_lattice3(sK0,X3,X4) )
    | ~ spl180_8 ),
    inference(resolution,[],[f4632,f3808])).

fof(f3808,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK78(X0,X1,X2,X3))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f3115])).

fof(f4632,plain,
    ( ! [X4] :
        ( r1_orders_2(sK0,sK3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r1_orders_2(sK0,sK1,X4) )
    | ~ spl180_8 ),
    inference(avatar_component_clause,[],[f4631])).

fof(f4633,plain,
    ( spl180_1
    | spl180_8 ),
    inference(avatar_split_clause,[],[f3428,f4631,f4597])).

fof(f3428,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK1,X4)
      | ~ r1_orders_2(sK0,sK2,X4)
      | r1_orders_2(sK0,sK3,X4)
      | sK3 = k13_lattice3(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f3026])).

fof(f4629,plain,
    ( ~ spl180_1
    | spl180_7
    | ~ spl180_2
    | ~ spl180_3 ),
    inference(avatar_split_clause,[],[f3429,f4606,f4601,f4626,f4597])).

fof(f3429,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | sK3 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3026])).

fof(f4624,plain,
    ( ~ spl180_1
    | spl180_6
    | ~ spl180_2
    | ~ spl180_3 ),
    inference(avatar_split_clause,[],[f3430,f4606,f4601,f4621,f4597])).

fof(f3430,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK1,sK4)
    | sK3 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3026])).

fof(f4619,plain,
    ( ~ spl180_1
    | spl180_5
    | ~ spl180_2
    | ~ spl180_3 ),
    inference(avatar_split_clause,[],[f3431,f4606,f4601,f4616,f4597])).

fof(f3431,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK4)
    | sK3 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3026])).

fof(f4614,plain,
    ( ~ spl180_1
    | ~ spl180_4
    | ~ spl180_2
    | ~ spl180_3 ),
    inference(avatar_split_clause,[],[f3432,f4606,f4601,f4611,f4597])).

fof(f3432,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK3,sK4)
    | sK3 != k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3026])).

fof(f4609,plain,
    ( spl180_1
    | spl180_3 ),
    inference(avatar_split_clause,[],[f3433,f4606,f4597])).

fof(f3433,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | sK3 = k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3026])).

fof(f4604,plain,
    ( spl180_1
    | spl180_2 ),
    inference(avatar_split_clause,[],[f3434,f4601,f4597])).

fof(f3434,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | sK3 = k13_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3026])).
%------------------------------------------------------------------------------
