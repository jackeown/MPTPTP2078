%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1545+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:23 EST 2020

% Result     : Theorem 9.95s
% Output     : Refutation 9.95s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 528 expanded)
%              Number of leaves         :   17 ( 119 expanded)
%              Depth                    :   28
%              Number of atoms          : 1012 (4635 expanded)
%              Number of equality atoms :   72 ( 366 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5506,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4436,f4441,f4446,f4451,f4456,f4461,f4465,f4898,f5051,f5282,f5387,f5436,f5482,f5498,f5505])).

fof(f5505,plain,
    ( spl166_1
    | ~ spl166_33 ),
    inference(avatar_contradiction_clause,[],[f5504])).

fof(f5504,plain,
    ( $false
    | spl166_1
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f4430,f5503])).

fof(f5503,plain,
    ( sK3 = k12_lattice3(sK0,sK1,sK2)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5502,f3406])).

fof(f3406,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3030])).

fof(f3030,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f3029])).

fof(f3029,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <~> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2987])).

fof(f2987,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( k12_lattice3(X0,X1,X2) = X3
                    <=> ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2986])).

fof(f2986,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

fof(f5502,plain,
    ( sK3 = k12_lattice3(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5501,f3404])).

fof(f3404,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5501,plain,
    ( sK3 = k12_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5500,f3405])).

fof(f3405,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5500,plain,
    ( sK3 = k12_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5499,f3408])).

fof(f3408,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5499,plain,
    ( sK3 = k12_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5452,f3407])).

fof(f3407,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5452,plain,
    ( sK3 = k12_lattice3(sK0,sK1,sK2)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl166_33 ),
    inference(superposition,[],[f3412,f4872])).

fof(f4872,plain,
    ( sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ spl166_33 ),
    inference(avatar_component_clause,[],[f4870])).

fof(f4870,plain,
    ( spl166_33
  <=> sK3 = k11_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_33])])).

fof(f3412,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3035])).

fof(f3035,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3034])).

fof(f3034,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2896])).

fof(f2896,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f4430,plain,
    ( sK3 != k12_lattice3(sK0,sK1,sK2)
    | spl166_1 ),
    inference(avatar_component_clause,[],[f4429])).

fof(f4429,plain,
    ( spl166_1
  <=> sK3 = k12_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_1])])).

fof(f5498,plain,
    ( spl166_2
    | ~ spl166_33 ),
    inference(avatar_contradiction_clause,[],[f5497])).

fof(f5497,plain,
    ( $false
    | spl166_2
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f4434,f5489])).

fof(f5489,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5488,f4467])).

fof(f4467,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4466,f3408])).

fof(f4466,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_struct_0(sK0) ),
    inference(resolution,[],[f3407,f3427])).

fof(f3427,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3043])).

fof(f3043,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3042])).

fof(f3042,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2807])).

fof(f2807,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f5488,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | v2_struct_0(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5487,f3403])).

fof(f3403,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3030])).

fof(f5487,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5486,f3404])).

fof(f5486,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5485,f3405])).

fof(f5485,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5484,f3408])).

fof(f5484,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5483,f3407])).

fof(f5483,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5457,f3406])).

fof(f5457,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl166_33 ),
    inference(superposition,[],[f4339,f4872])).

fof(f4339,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3752])).

fof(f3752,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f3109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3108])).

fof(f3108,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2893])).

fof(f2893,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f4434,plain,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | spl166_2 ),
    inference(avatar_component_clause,[],[f4433])).

fof(f4433,plain,
    ( spl166_2
  <=> r1_orders_2(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_2])])).

fof(f5482,plain,
    ( spl166_3
    | ~ spl166_33 ),
    inference(avatar_contradiction_clause,[],[f5481])).

fof(f5481,plain,
    ( $false
    | spl166_3
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5480,f4467])).

fof(f5480,plain,
    ( v2_struct_0(sK0)
    | spl166_3
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5479,f3403])).

fof(f5479,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl166_3
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5478,f3404])).

fof(f5478,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl166_3
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5477,f3405])).

fof(f5477,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl166_3
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5476,f3408])).

fof(f5476,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl166_3
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5475,f3407])).

fof(f5475,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl166_3
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5474,f3406])).

fof(f5474,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl166_3
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5458,f4439])).

fof(f4439,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | spl166_3 ),
    inference(avatar_component_clause,[],[f4438])).

fof(f4438,plain,
    ( spl166_3
  <=> r1_orders_2(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_3])])).

fof(f5458,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl166_33 ),
    inference(superposition,[],[f4340,f4872])).

fof(f4340,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3751])).

fof(f3751,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X1)
      | k11_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f3109])).

fof(f5436,plain,
    ( ~ spl166_1
    | spl166_33 ),
    inference(avatar_contradiction_clause,[],[f5435])).

fof(f5435,plain,
    ( $false
    | ~ spl166_1
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5434,f3406])).

fof(f5434,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl166_1
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5433,f3404])).

fof(f5433,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl166_1
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5432,f3405])).

fof(f5432,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl166_1
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5431,f3408])).

fof(f5431,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl166_1
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5430,f3407])).

fof(f5430,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl166_1
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5429,f4431])).

fof(f4431,plain,
    ( sK3 = k12_lattice3(sK0,sK1,sK2)
    | ~ spl166_1 ),
    inference(avatar_component_clause,[],[f4429])).

fof(f5429,plain,
    ( sK3 != k12_lattice3(sK0,sK1,sK2)
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl166_33 ),
    inference(superposition,[],[f4871,f3412])).

fof(f4871,plain,
    ( sK3 != k11_lattice3(sK0,sK1,sK2)
    | spl166_33 ),
    inference(avatar_component_clause,[],[f4870])).

fof(f5387,plain,
    ( spl166_4
    | ~ spl166_5
    | ~ spl166_6
    | ~ spl166_7
    | ~ spl166_31
    | ~ spl166_33 ),
    inference(avatar_contradiction_clause,[],[f5386])).

fof(f5386,plain,
    ( $false
    | spl166_4
    | ~ spl166_5
    | ~ spl166_6
    | ~ spl166_7
    | ~ spl166_31
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5385,f4450])).

fof(f4450,plain,
    ( r1_orders_2(sK0,sK4,sK2)
    | ~ spl166_5 ),
    inference(avatar_component_clause,[],[f4448])).

fof(f4448,plain,
    ( spl166_5
  <=> r1_orders_2(sK0,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_5])])).

fof(f5385,plain,
    ( ~ r1_orders_2(sK0,sK4,sK2)
    | spl166_4
    | ~ spl166_6
    | ~ spl166_7
    | ~ spl166_31
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5384,f4455])).

fof(f4455,plain,
    ( r1_orders_2(sK0,sK4,sK1)
    | ~ spl166_6 ),
    inference(avatar_component_clause,[],[f4453])).

fof(f4453,plain,
    ( spl166_6
  <=> r1_orders_2(sK0,sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_6])])).

fof(f5384,plain,
    ( ~ r1_orders_2(sK0,sK4,sK1)
    | ~ r1_orders_2(sK0,sK4,sK2)
    | spl166_4
    | ~ spl166_7
    | ~ spl166_31
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5367,f4460])).

fof(f4460,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl166_7 ),
    inference(avatar_component_clause,[],[f4458])).

fof(f4458,plain,
    ( spl166_7
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_7])])).

fof(f5367,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK4,sK1)
    | ~ r1_orders_2(sK0,sK4,sK2)
    | spl166_4
    | ~ spl166_31
    | ~ spl166_33 ),
    inference(resolution,[],[f5364,f4445])).

fof(f4445,plain,
    ( ~ r1_orders_2(sK0,sK4,sK3)
    | spl166_4 ),
    inference(avatar_component_clause,[],[f4443])).

fof(f4443,plain,
    ( spl166_4
  <=> r1_orders_2(sK0,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_4])])).

fof(f5364,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2) )
    | ~ spl166_31
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5363,f3406])).

fof(f5363,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ v5_orders_2(sK0) )
    | ~ spl166_31
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5362,f4856])).

fof(f4856,plain,
    ( r2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl166_31 ),
    inference(avatar_component_clause,[],[f4854])).

fof(f4854,plain,
    ( spl166_31
  <=> r2_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_31])])).

fof(f5362,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ v5_orders_2(sK0) )
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5361,f3403])).

fof(f5361,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ v5_orders_2(sK0) )
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5360,f3404])).

fof(f5360,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ v5_orders_2(sK0) )
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5359,f3405])).

fof(f5359,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ v5_orders_2(sK0) )
    | ~ spl166_33 ),
    inference(subsumption_resolution,[],[f5355,f3408])).

fof(f5355,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ v5_orders_2(sK0) )
    | ~ spl166_33 ),
    inference(superposition,[],[f4338,f4872])).

fof(f4338,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3734])).

fof(f3734,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X5,X1)
      | ~ r1_orders_2(X0,X5,X2)
      | r1_orders_2(X0,X5,X3) ) ),
    inference(cnf_transformation,[],[f3105])).

fof(f3105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3104])).

fof(f3104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3000])).

fof(f3000,plain,(
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
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X5,X2)
                                & r1_orders_2(X0,X5,X1) )
                             => r1_orders_2(X0,X5,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f2981])).

fof(f2981,axiom,(
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
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_0)).

fof(f5282,plain,
    ( ~ spl166_2
    | ~ spl166_3
    | ~ spl166_8
    | ~ spl166_32
    | spl166_33 ),
    inference(avatar_contradiction_clause,[],[f5281])).

fof(f5281,plain,
    ( $false
    | ~ spl166_2
    | ~ spl166_3
    | ~ spl166_8
    | ~ spl166_32
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5280,f3406])).

fof(f5280,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl166_2
    | ~ spl166_3
    | ~ spl166_8
    | ~ spl166_32
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5279,f4435])).

fof(f4435,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | ~ spl166_2 ),
    inference(avatar_component_clause,[],[f4433])).

fof(f5279,plain,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl166_2
    | ~ spl166_3
    | ~ spl166_8
    | ~ spl166_32
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5278,f3403])).

fof(f5278,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl166_2
    | ~ spl166_3
    | ~ spl166_8
    | ~ spl166_32
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5277,f3404])).

fof(f5277,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl166_2
    | ~ spl166_3
    | ~ spl166_8
    | ~ spl166_32
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5276,f3408])).

fof(f5276,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl166_2
    | ~ spl166_3
    | ~ spl166_8
    | ~ spl166_32
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5275,f4871])).

fof(f5275,plain,
    ( sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl166_2
    | ~ spl166_3
    | ~ spl166_8
    | ~ spl166_32 ),
    inference(subsumption_resolution,[],[f5274,f4440])).

fof(f4440,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | ~ spl166_3 ),
    inference(avatar_component_clause,[],[f4438])).

fof(f5274,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl166_2
    | ~ spl166_8
    | ~ spl166_32 ),
    inference(subsumption_resolution,[],[f5273,f3405])).

fof(f5273,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl166_2
    | ~ spl166_8
    | ~ spl166_32 ),
    inference(subsumption_resolution,[],[f5271,f4859])).

fof(f4859,plain,
    ( m1_subset_1(sK73(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl166_32 ),
    inference(avatar_component_clause,[],[f4858])).

fof(f4858,plain,
    ( spl166_32
  <=> m1_subset_1(sK73(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_32])])).

fof(f5271,plain,
    ( ~ m1_subset_1(sK73(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | ~ spl166_2
    | ~ spl166_8 ),
    inference(duplicate_literal_removal,[],[f5270])).

fof(f5270,plain,
    ( ~ m1_subset_1(sK73(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ spl166_2
    | ~ spl166_8 ),
    inference(resolution,[],[f4886,f3740])).

fof(f3740,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK73(X0,X1,X2,X3),X1)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f3105])).

fof(f4886,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK73(sK0,X1,sK2,sK3),sK1)
        | ~ m1_subset_1(sK73(sK0,X1,sK2,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X1)
        | sK3 = k11_lattice3(sK0,X1,sK2) )
    | ~ spl166_2
    | ~ spl166_8 ),
    inference(subsumption_resolution,[],[f4885,f3406])).

fof(f4885,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK73(sK0,X1,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X1,sK2,sK3),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X1)
        | sK3 = k11_lattice3(sK0,X1,sK2)
        | ~ v5_orders_2(sK0) )
    | ~ spl166_2
    | ~ spl166_8 ),
    inference(subsumption_resolution,[],[f4884,f3403])).

fof(f4884,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK73(sK0,X1,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X1,sK2,sK3),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X1)
        | sK3 = k11_lattice3(sK0,X1,sK2)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0) )
    | ~ spl166_2
    | ~ spl166_8 ),
    inference(subsumption_resolution,[],[f4883,f3408])).

fof(f4883,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK73(sK0,X1,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X1,sK2,sK3),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X1)
        | sK3 = k11_lattice3(sK0,X1,sK2)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0) )
    | ~ spl166_2
    | ~ spl166_8 ),
    inference(subsumption_resolution,[],[f4882,f4435])).

fof(f4882,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK73(sK0,X1,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X1,sK2,sK3),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X1)
        | ~ r1_orders_2(sK0,sK3,sK2)
        | sK3 = k11_lattice3(sK0,X1,sK2)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0) )
    | ~ spl166_8 ),
    inference(subsumption_resolution,[],[f4880,f3404])).

fof(f4880,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK73(sK0,X1,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X1,sK2,sK3),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X1)
        | ~ r1_orders_2(sK0,sK3,sK2)
        | sK3 = k11_lattice3(sK0,X1,sK2)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0) )
    | ~ spl166_8 ),
    inference(duplicate_literal_removal,[],[f4875])).

fof(f4875,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK73(sK0,X1,sK2,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X1,sK2,sK3),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X1)
        | ~ r1_orders_2(sK0,sK3,sK2)
        | sK3 = k11_lattice3(sK0,X1,sK2)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X1)
        | ~ r1_orders_2(sK0,sK3,sK2)
        | ~ v5_orders_2(sK0)
        | sK3 = k11_lattice3(sK0,X1,sK2) )
    | ~ spl166_8 ),
    inference(resolution,[],[f4551,f3741])).

fof(f3741,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK73(X0,X1,X2,X3),X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f3105])).

fof(f4551,plain,
    ( ! [X4,X3] :
        ( ~ r1_orders_2(sK0,sK73(sK0,X3,X4,sK3),sK2)
        | ~ m1_subset_1(sK73(sK0,X3,X4,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X3,X4,sK3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X3)
        | ~ r1_orders_2(sK0,sK3,X4)
        | sK3 = k11_lattice3(sK0,X3,X4) )
    | ~ spl166_8 ),
    inference(subsumption_resolution,[],[f4550,f3406])).

fof(f4550,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK73(sK0,X3,X4,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X3,X4,sK3),sK2)
        | ~ r1_orders_2(sK0,sK73(sK0,X3,X4,sK3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X3)
        | ~ r1_orders_2(sK0,sK3,X4)
        | ~ v5_orders_2(sK0)
        | sK3 = k11_lattice3(sK0,X3,X4) )
    | ~ spl166_8 ),
    inference(subsumption_resolution,[],[f4549,f3403])).

fof(f4549,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK73(sK0,X3,X4,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X3,X4,sK3),sK2)
        | ~ r1_orders_2(sK0,sK73(sK0,X3,X4,sK3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X3)
        | ~ r1_orders_2(sK0,sK3,X4)
        | ~ v5_orders_2(sK0)
        | sK3 = k11_lattice3(sK0,X3,X4) )
    | ~ spl166_8 ),
    inference(subsumption_resolution,[],[f4530,f3408])).

fof(f4530,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK73(sK0,X3,X4,sK3),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK73(sK0,X3,X4,sK3),sK2)
        | ~ r1_orders_2(sK0,sK73(sK0,X3,X4,sK3),sK1)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3,X3)
        | ~ r1_orders_2(sK0,sK3,X4)
        | ~ v5_orders_2(sK0)
        | sK3 = k11_lattice3(sK0,X3,X4) )
    | ~ spl166_8 ),
    inference(resolution,[],[f4464,f3742])).

fof(f3742,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK73(X0,X1,X2,X3),X3)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f3105])).

fof(f4464,plain,
    ( ! [X4] :
        ( r1_orders_2(sK0,X4,sK3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,sK2)
        | ~ r1_orders_2(sK0,X4,sK1) )
    | ~ spl166_8 ),
    inference(avatar_component_clause,[],[f4463])).

fof(f4463,plain,
    ( spl166_8
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_orders_2(sK0,X4,sK3)
        | ~ r1_orders_2(sK0,X4,sK2)
        | ~ r1_orders_2(sK0,X4,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl166_8])])).

fof(f5051,plain,
    ( ~ spl166_2
    | ~ spl166_3
    | spl166_32
    | spl166_33 ),
    inference(avatar_contradiction_clause,[],[f5050])).

fof(f5050,plain,
    ( $false
    | ~ spl166_2
    | ~ spl166_3
    | spl166_32
    | spl166_33 ),
    inference(subsumption_resolution,[],[f5049,f4871])).

fof(f5049,plain,
    ( sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ spl166_2
    | ~ spl166_3
    | spl166_32 ),
    inference(subsumption_resolution,[],[f5048,f3406])).

fof(f5048,plain,
    ( ~ v5_orders_2(sK0)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ spl166_2
    | ~ spl166_3
    | spl166_32 ),
    inference(subsumption_resolution,[],[f5047,f4435])).

fof(f5047,plain,
    ( ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | ~ spl166_3
    | spl166_32 ),
    inference(subsumption_resolution,[],[f5046,f4440])).

fof(f5046,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | spl166_32 ),
    inference(subsumption_resolution,[],[f5045,f3403])).

fof(f5045,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | spl166_32 ),
    inference(subsumption_resolution,[],[f5044,f3404])).

fof(f5044,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | spl166_32 ),
    inference(subsumption_resolution,[],[f5043,f3405])).

fof(f5043,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | spl166_32 ),
    inference(subsumption_resolution,[],[f5039,f3408])).

fof(f5039,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ v5_orders_2(sK0)
    | sK3 = k11_lattice3(sK0,sK1,sK2)
    | spl166_32 ),
    inference(resolution,[],[f4860,f3739])).

fof(f3739,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK73(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f3105])).

fof(f4860,plain,
    ( ~ m1_subset_1(sK73(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | spl166_32 ),
    inference(avatar_component_clause,[],[f4858])).

fof(f4898,plain,(
    spl166_31 ),
    inference(avatar_contradiction_clause,[],[f4897])).

fof(f4897,plain,
    ( $false
    | spl166_31 ),
    inference(subsumption_resolution,[],[f4896,f3407])).

fof(f4896,plain,
    ( ~ v2_lattice3(sK0)
    | spl166_31 ),
    inference(subsumption_resolution,[],[f4895,f3406])).

fof(f4895,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | spl166_31 ),
    inference(subsumption_resolution,[],[f4894,f3404])).

fof(f4894,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | spl166_31 ),
    inference(subsumption_resolution,[],[f4893,f3405])).

fof(f4893,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | spl166_31 ),
    inference(subsumption_resolution,[],[f4892,f3408])).

fof(f4892,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | spl166_31 ),
    inference(resolution,[],[f4855,f4204])).

fof(f4204,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f3363])).

fof(f3363,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3362])).

fof(f3362,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2984])).

fof(f2984,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_0)).

fof(f4855,plain,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | spl166_31 ),
    inference(avatar_component_clause,[],[f4854])).

fof(f4465,plain,
    ( spl166_1
    | spl166_8 ),
    inference(avatar_split_clause,[],[f3396,f4463,f4429])).

fof(f3396,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X4,sK1)
      | ~ r1_orders_2(sK0,X4,sK2)
      | r1_orders_2(sK0,X4,sK3)
      | sK3 = k12_lattice3(sK0,sK1,sK2) ) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4461,plain,
    ( ~ spl166_1
    | spl166_7
    | ~ spl166_2
    | ~ spl166_3 ),
    inference(avatar_split_clause,[],[f3397,f4438,f4433,f4458,f4429])).

fof(f3397,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | sK3 != k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4456,plain,
    ( ~ spl166_1
    | spl166_6
    | ~ spl166_2
    | ~ spl166_3 ),
    inference(avatar_split_clause,[],[f3398,f4438,f4433,f4453,f4429])).

fof(f3398,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | r1_orders_2(sK0,sK4,sK1)
    | sK3 != k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4451,plain,
    ( ~ spl166_1
    | spl166_5
    | ~ spl166_2
    | ~ spl166_3 ),
    inference(avatar_split_clause,[],[f3399,f4438,f4433,f4448,f4429])).

fof(f3399,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | r1_orders_2(sK0,sK4,sK2)
    | sK3 != k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4446,plain,
    ( ~ spl166_1
    | ~ spl166_4
    | ~ spl166_2
    | ~ spl166_3 ),
    inference(avatar_split_clause,[],[f3400,f4438,f4433,f4443,f4429])).

fof(f3400,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK3,sK2)
    | ~ r1_orders_2(sK0,sK4,sK3)
    | sK3 != k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4441,plain,
    ( spl166_1
    | spl166_3 ),
    inference(avatar_split_clause,[],[f3401,f4438,f4429])).

fof(f3401,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | sK3 = k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3030])).

fof(f4436,plain,
    ( spl166_1
    | spl166_2 ),
    inference(avatar_split_clause,[],[f3402,f4433,f4429])).

fof(f3402,plain,
    ( r1_orders_2(sK0,sK3,sK2)
    | sK3 = k12_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3030])).
%------------------------------------------------------------------------------
