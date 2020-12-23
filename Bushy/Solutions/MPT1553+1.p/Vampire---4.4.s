%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t31_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:40 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 380 expanded)
%              Number of leaves         :   24 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          :  633 (2062 expanded)
%              Number of equality atoms :   36 ( 193 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f567,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f61,f72,f86,f105,f156,f175,f179,f263,f332,f344,f450,f464,f474,f478,f490,f551,f565,f566])).

fof(f566,plain,
    ( k2_yellow_0(sK0,sK2) != sK1
    | r1_lattice3(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) ),
    introduced(theory_axiom,[])).

fof(f565,plain,
    ( spl10_12
    | spl10_50
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f553,f154,f70,f59,f54,f379,f84])).

fof(f84,plain,
    ( spl10_12
  <=> k2_yellow_0(sK0,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f379,plain,
    ( spl10_50
  <=> m1_subset_1(sK7(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f54,plain,
    ( spl10_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f59,plain,
    ( spl10_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f70,plain,
    ( spl10_8
  <=> r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f154,plain,
    ( spl10_16
  <=> r1_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f553,plain,
    ( m1_subset_1(sK7(sK0,sK2,sK1),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f552,f55])).

fof(f55,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f552,plain,
    ( ~ l1_orders_2(sK0)
    | m1_subset_1(sK7(sK0,sK2,sK1),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f325,f71])).

fof(f71,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f325,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | m1_subset_1(sK7(sK0,sK2,sK1),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_4
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f158,f60])).

fof(f60,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f158,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | m1_subset_1(sK7(sK0,sK2,sK1),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_16 ),
    inference(resolution,[],[f155,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t31_yellow_0.p',d10_yellow_0)).

fof(f155,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f551,plain,
    ( spl10_12
    | spl10_48
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f505,f154,f70,f59,f54,f346,f84])).

fof(f346,plain,
    ( spl10_48
  <=> r1_lattice3(sK0,sK2,sK7(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f505,plain,
    ( r1_lattice3(sK0,sK2,sK7(sK0,sK2,sK1))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f504,f55])).

fof(f504,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK7(sK0,sK2,sK1))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f322,f71])).

fof(f322,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK7(sK0,sK2,sK1))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_4
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f159,f60])).

fof(f159,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK7(sK0,sK2,sK1))
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_16 ),
    inference(resolution,[],[f155,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f490,plain,
    ( ~ spl10_2
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_14
    | spl10_83
    | ~ spl10_84 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_83
    | ~ spl10_84 ),
    inference(subsumption_resolution,[],[f488,f473])).

fof(f473,plain,
    ( ~ r1_orders_2(sK0,sK4,sK1)
    | ~ spl10_83 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl10_83
  <=> ~ r1_orders_2(sK0,sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f488,plain,
    ( r1_orders_2(sK0,sK4,sK1)
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_84 ),
    inference(forward_demodulation,[],[f487,f85])).

fof(f85,plain,
    ( k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f487,plain,
    ( r1_orders_2(sK0,sK4,k2_yellow_0(sK0,sK2))
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_14
    | ~ spl10_84 ),
    inference(subsumption_resolution,[],[f486,f71])).

fof(f486,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | r1_orders_2(sK0,sK4,k2_yellow_0(sK0,sK2))
    | ~ spl10_2
    | ~ spl10_14
    | ~ spl10_84 ),
    inference(subsumption_resolution,[],[f479,f101])).

fof(f101,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl10_14
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f479,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK2)
    | r1_orders_2(sK0,sK4,k2_yellow_0(sK0,sK2))
    | ~ spl10_2
    | ~ spl10_84 ),
    inference(resolution,[],[f477,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,X0)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f62,f55])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,
    ( ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))
    | ~ spl10_2 ),
    inference(resolution,[],[f55,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t31_yellow_0.p',dt_k2_yellow_0)).

fof(f477,plain,
    ( r1_lattice3(sK0,sK2,sK4)
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f476])).

fof(f476,plain,
    ( spl10_84
  <=> r1_lattice3(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f478,plain,
    ( spl10_84
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f470,f154,f84,f70,f476])).

fof(f470,plain,
    ( r1_lattice3(sK0,sK2,sK4)
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f467,f91])).

fof(f91,plain,
    ( ~ sP3(sK2,sK1,sK0)
    | ~ spl10_8
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f90,f71])).

fof(f90,plain,
    ( ~ sP3(sK2,sK1,sK0)
    | ~ r2_yellow_0(sK0,sK2)
    | ~ spl10_12 ),
    inference(superposition,[],[f46,f85])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ sP3(X2,k2_yellow_0(X0,X2),X0)
      | ~ r2_yellow_0(X0,X2) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) != X1
      | ~ r2_yellow_0(X0,X2)
      | ~ sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_yellow_0(X0,X2)
                  | k2_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X1)
                      & r1_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X2,X1) )
                & r2_yellow_0(X0,X2)
                & k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r2_yellow_0(X0,X2)
                  | k2_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | ~ r1_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X1)
                      & r1_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X2,X1) )
                & r2_yellow_0(X0,X2)
                & k2_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r1_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X3,X1) ) )
                    & r1_lattice3(X0,X2,X1) )
                 => ( r2_yellow_0(X0,X2)
                    & k2_yellow_0(X0,X2) = X1 ) )
                & ( ( r2_yellow_0(X0,X2)
                    & k2_yellow_0(X0,X2) = X1 )
                 => ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_lattice3(X0,X2,X4)
                         => r1_orders_2(X0,X4,X1) ) )
                    & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r1_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X3,X1) ) )
                    & r1_lattice3(X0,X2,X1) )
                 => ( r2_yellow_0(X0,X2)
                    & k2_yellow_0(X0,X2) = X1 ) )
                & ( ( r2_yellow_0(X0,X2)
                    & k2_yellow_0(X0,X2) = X1 )
                 => ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r1_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X3,X1) ) )
                    & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t31_yellow_0.p',t31_yellow_0)).

fof(f467,plain,
    ( r1_lattice3(sK0,sK2,sK4)
    | sP3(sK2,sK1,sK0)
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f23,f155])).

fof(f23,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | r1_lattice3(sK0,sK2,sK4)
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f474,plain,
    ( ~ spl10_83
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f469,f154,f84,f70,f472])).

fof(f469,plain,
    ( ~ r1_orders_2(sK0,sK4,sK1)
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f468,f91])).

fof(f468,plain,
    ( ~ r1_orders_2(sK0,sK4,sK1)
    | sP3(sK2,sK1,sK0)
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f24,f155])).

fof(f24,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK4,sK1)
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f464,plain,
    ( spl10_12
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(avatar_split_clause,[],[f456,f448,f154,f70,f59,f54,f84])).

fof(f448,plain,
    ( spl10_76
  <=> r1_orders_2(sK0,sK7(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f456,plain,
    ( k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f455,f55])).

fof(f455,plain,
    ( ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f454,f155])).

fof(f454,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f453,f71])).

fof(f453,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_4
    | ~ spl10_76 ),
    inference(subsumption_resolution,[],[f452,f60])).

fof(f452,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK2)
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,sK2) = sK1
    | ~ spl10_76 ),
    inference(resolution,[],[f449,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK7(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f449,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK2,sK1),sK1)
    | ~ spl10_76 ),
    inference(avatar_component_clause,[],[f448])).

fof(f450,plain,
    ( spl10_76
    | ~ spl10_6
    | ~ spl10_48
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f446,f379,f346,f67,f448])).

fof(f67,plain,
    ( spl10_6
  <=> sP3(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f446,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK2,sK1),sK1)
    | ~ spl10_6
    | ~ spl10_48
    | ~ spl10_50 ),
    inference(resolution,[],[f385,f68])).

fof(f68,plain,
    ( sP3(sK2,sK1,sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ sP3(sK2,X0,sK0)
        | r1_orders_2(sK0,sK7(sK0,sK2,sK1),X0) )
    | ~ spl10_48
    | ~ spl10_50 ),
    inference(subsumption_resolution,[],[f350,f380])).

fof(f380,plain,
    ( m1_subset_1(sK7(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f379])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK0,sK2,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK7(sK0,sK2,sK1),X0)
        | ~ sP3(sK2,X0,sK0) )
    | ~ spl10_48 ),
    inference(resolution,[],[f347,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,X1)
      | ~ sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f347,plain,
    ( r1_lattice3(sK0,sK2,sK7(sK0,sK2,sK1))
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f346])).

fof(f344,plain,
    ( spl10_46
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f333,f70,f54,f342])).

fof(f342,plain,
    ( spl10_46
  <=> r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f333,plain,
    ( r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | ~ spl10_2
    | ~ spl10_8 ),
    inference(resolution,[],[f71,f65])).

fof(f65,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f63,f55])).

fof(f63,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f57,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f332,plain,
    ( spl10_8
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f272,f261,f154,f59,f54,f50,f70])).

fof(f50,plain,
    ( spl10_0
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f261,plain,
    ( spl10_38
  <=> r1_orders_2(sK0,sK6(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f272,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f271,f51])).

fof(f51,plain,
    ( v5_orders_2(sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f50])).

fof(f271,plain,
    ( ~ v5_orders_2(sK0)
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f270,f155])).

fof(f270,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0)
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f269,f60])).

fof(f269,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0)
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_2
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f268,f55])).

fof(f268,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0)
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_38 ),
    inference(resolution,[],[f262,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t31_yellow_0.p',t16_yellow_0)).

fof(f262,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK2,sK1),sK1)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f261])).

fof(f263,plain,
    ( spl10_38
    | ~ spl10_6
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f259,f177,f173,f67,f261])).

fof(f173,plain,
    ( spl10_22
  <=> m1_subset_1(sK6(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f177,plain,
    ( spl10_24
  <=> r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f259,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK2,sK1),sK1)
    | ~ spl10_6
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(resolution,[],[f186,f68])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ sP3(sK2,X0,sK0)
        | r1_orders_2(sK0,sK6(sK0,sK2,sK1),X0) )
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f180,f174])).

fof(f174,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,sK2,sK1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,sK2,sK1),X0)
        | ~ sP3(sK2,X0,sK0) )
    | ~ spl10_24 ),
    inference(resolution,[],[f178,f21])).

fof(f178,plain,
    ( r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK1))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,
    ( spl10_24
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | spl10_9
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f171,f154,f150,f59,f54,f50,f177])).

fof(f150,plain,
    ( spl10_9
  <=> ~ r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f171,plain,
    ( r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK1))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f170,f151])).

fof(f151,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f170,plain,
    ( r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK1))
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f169,f51])).

fof(f169,plain,
    ( ~ v5_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK1))
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f168,f60])).

fof(f168,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK1))
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_2
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f161,f55])).

fof(f161,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK6(sK0,sK2,sK1))
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_16 ),
    inference(resolution,[],[f155,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f175,plain,
    ( spl10_22
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | spl10_9
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f167,f154,f150,f59,f54,f50,f173])).

fof(f167,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_9
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f166,f151])).

fof(f166,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK1),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f165,f51])).

fof(f165,plain,
    ( ~ v5_orders_2(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK1),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f164,f60])).

fof(f164,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK1),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_2
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f160,f55])).

fof(f160,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | m1_subset_1(sK6(sK0,sK2,sK1),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK2)
    | ~ spl10_16 ),
    inference(resolution,[],[f155,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f156,plain,
    ( spl10_16
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f146,f67,f154])).

fof(f146,plain,
    ( r1_lattice3(sK0,sK2,sK1)
    | ~ spl10_6 ),
    inference(resolution,[],[f68,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X1,X0)
      | r1_lattice3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f105,plain,
    ( spl10_14
    | ~ spl10_17
    | ~ spl10_8
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f92,f84,f70,f103,f100])).

fof(f103,plain,
    ( spl10_17
  <=> ~ r1_lattice3(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f92,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl10_8
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f22,f91])).

fof(f22,plain,
    ( ~ r1_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK4,u1_struct_0(sK0))
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,
    ( spl10_6
    | spl10_12 ),
    inference(avatar_split_clause,[],[f27,f84,f67])).

fof(f27,plain,
    ( k2_yellow_0(sK0,sK2) = sK1
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,
    ( spl10_6
    | spl10_8 ),
    inference(avatar_split_clause,[],[f28,f70,f67])).

fof(f28,plain,
    ( r2_yellow_0(sK0,sK2)
    | sP3(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f31,f54])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f30,f50])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
