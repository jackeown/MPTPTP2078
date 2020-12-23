%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  304 ( 677 expanded)
%              Number of leaves         :   49 ( 263 expanded)
%              Depth                    :   27
%              Number of atoms          : 2398 (4759 expanded)
%              Number of equality atoms :   85 ( 211 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f513,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f173,f178,f183,f188,f193,f203,f208,f245,f254,f259,f275,f296,f315,f334,f338,f407,f427,f438,f446,f457,f468,f488,f511])).

fof(f511,plain,
    ( ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_29
    | spl6_40
    | ~ spl6_42 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_29
    | spl6_40
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f509,f177])).

fof(f177,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f175])).

% (19585)Refutation not found, incomplete strategy% (19585)------------------------------
% (19585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f175,plain,
    ( spl6_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

% (19585)Termination reason: Refutation not found, incomplete strategy

% (19585)Memory used [KB]: 10874
fof(f509,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_29
    | spl6_40
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f508,f397])).

% (19585)Time elapsed: 0.075 s
% (19585)------------------------------
% (19585)------------------------------
fof(f397,plain,
    ( sK1 != k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | spl6_40 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl6_40
  <=> sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f508,plain,
    ( sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_29
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f507,f314])).

fof(f314,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl6_29
  <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f507,plain,
    ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_25
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f506,f405])).

fof(f405,plain,
    ( m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl6_42
  <=> m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f506,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_25 ),
    inference(duplicate_literal_removal,[],[f504])).

fof(f504,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_25 ),
    inference(resolution,[],[f498,f211])).

fof(f211,plain,
    ( ! [X4,X5] :
        ( r1_lattice3(sK0,X5,sK5(sK0,X4,X5))
        | ~ r1_lattice3(sK0,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k2_yellow_0(sK0,X5) = X4 )
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f165,f187])).

fof(f187,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_18
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f165,plain,
    ( ! [X4,X5] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X5,X4)
        | r1_lattice3(sK0,X5,sK5(sK0,X4,X5))
        | k2_yellow_0(sK0,X5) = X4 )
    | ~ spl6_8 ),
    inference(resolution,[],[f125,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | r1_lattice3(X0,X2,sK5(X0,X1,X2))
      | k2_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f125,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_8
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))
        | ~ m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,sK1)
        | sK1 = k2_yellow_0(sK0,X0) )
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f497,f177])).

fof(f497,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))
        | ~ r1_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | sK1 = k2_yellow_0(sK0,X0) )
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_25 ),
    inference(resolution,[],[f491,f213])).

fof(f213,plain,
    ( ! [X6,X7] :
        ( ~ r1_orders_2(sK0,sK5(sK0,X6,X7),X6)
        | ~ r1_lattice3(sK0,X7,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k2_yellow_0(sK0,X7) = X6 )
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f166,f187])).

fof(f166,plain,
    ( ! [X6,X7] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X7,X6)
        | ~ r1_orders_2(sK0,sK5(sK0,X6,X7),X6)
        | k2_yellow_0(sK0,X7) = X6 )
    | ~ spl6_8 ),
    inference(resolution,[],[f125,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X1)
      | k2_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f491,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f490,f177])).

fof(f490,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK1)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0)) )
    | ~ spl6_15
    | ~ spl6_25 ),
    inference(resolution,[],[f253,f172])).

fof(f172,plain,
    ( r3_waybel_9(sK0,sK2,sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl6_15
  <=> r3_waybel_9(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl6_25
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | ~ r3_waybel_9(sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f488,plain,
    ( ~ spl6_8
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_29
    | spl6_40
    | spl6_41 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_29
    | spl6_40
    | spl6_41 ),
    inference(subsumption_resolution,[],[f486,f397])).

fof(f486,plain,
    ( sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_29
    | spl6_41 ),
    inference(subsumption_resolution,[],[f485,f177])).

fof(f485,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_29
    | spl6_41 ),
    inference(subsumption_resolution,[],[f483,f314])).

fof(f483,plain,
    ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl6_8
    | ~ spl6_18
    | spl6_41 ),
    inference(resolution,[],[f402,f211])).

fof(f402,plain,
    ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))))
    | spl6_41 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl6_41
  <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f468,plain,
    ( ~ spl6_13
    | ~ spl6_18
    | spl6_19
    | spl6_21
    | ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_18
    | spl6_19
    | spl6_21
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f466,f150])).

fof(f150,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_13
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f466,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ spl6_18
    | spl6_19
    | spl6_21
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f462,f192])).

fof(f192,plain,
    ( sK1 != k1_waybel_9(sK0,sK2)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_19
  <=> sK1 = k1_waybel_9(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f462,plain,
    ( sK1 = k1_waybel_9(sK0,sK2)
    | ~ l1_waybel_0(sK2,sK0)
    | ~ spl6_18
    | spl6_21
    | ~ spl6_39 ),
    inference(superposition,[],[f212,f378])).

fof(f378,plain,
    ( sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl6_39
  <=> sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f212,plain,
    ( ! [X0] :
        ( k1_waybel_9(sK0,X0) = k5_yellow_2(sK0,u1_waybel_0(sK0,X0))
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl6_18
    | spl6_21 ),
    inference(subsumption_resolution,[],[f194,f201])).

fof(f201,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_21
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f194,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_waybel_0(X0,sK0)
        | k1_waybel_9(sK0,X0) = k5_yellow_2(sK0,u1_waybel_0(sK0,X0)) )
    | ~ spl6_18 ),
    inference(resolution,[],[f187,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_9)).

fof(f457,plain,
    ( sK1 != k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) != k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f446,plain,
    ( ~ spl6_30
    | ~ spl6_40
    | spl6_43 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl6_30
    | ~ spl6_40
    | spl6_43 ),
    inference(subsumption_resolution,[],[f444,f319])).

fof(f319,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl6_30
  <=> m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f444,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl6_40
    | spl6_43 ),
    inference(subsumption_resolution,[],[f441,f413])).

fof(f413,plain,
    ( sK1 != k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | spl6_43 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl6_43
  <=> sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f441,plain,
    ( sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl6_40 ),
    inference(superposition,[],[f398,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f398,plain,
    ( sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f396])).

fof(f438,plain,
    ( spl6_29
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f433,f243,f175,f170,f312])).

fof(f243,plain,
    ( spl6_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ r3_waybel_9(sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f433,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f432,f177])).

fof(f432,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_15
    | ~ spl6_23 ),
    inference(resolution,[],[f244,f172])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f243])).

fof(f427,plain,
    ( ~ spl6_8
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_29
    | spl6_40
    | spl6_42 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_29
    | spl6_40
    | spl6_42 ),
    inference(subsumption_resolution,[],[f425,f397])).

fof(f425,plain,
    ( sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl6_8
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_29
    | spl6_42 ),
    inference(subsumption_resolution,[],[f424,f125])).

fof(f424,plain,
    ( ~ v5_orders_2(sK0)
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl6_16
    | ~ spl6_18
    | ~ spl6_29
    | spl6_42 ),
    inference(subsumption_resolution,[],[f423,f314])).

fof(f423,plain,
    ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl6_16
    | ~ spl6_18
    | spl6_42 ),
    inference(subsumption_resolution,[],[f422,f177])).

fof(f422,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | ~ spl6_18
    | spl6_42 ),
    inference(subsumption_resolution,[],[f416,f187])).

fof(f416,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | ~ v5_orders_2(sK0)
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | spl6_42 ),
    inference(resolution,[],[f406,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0)
      | k2_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f406,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | spl6_42 ),
    inference(avatar_component_clause,[],[f404])).

fof(f407,plain,
    ( spl6_40
    | ~ spl6_41
    | ~ spl6_42
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | spl6_27
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f335,f312,f272,f185,f175,f170,f148,f143,f138,f133,f128,f123,f118,f113,f108,f103,f98,f93,f88,f404,f400,f396])).

fof(f88,plain,
    ( spl6_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f93,plain,
    ( spl6_2
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f98,plain,
    ( spl6_3
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f103,plain,
    ( spl6_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f108,plain,
    ( spl6_5
  <=> v8_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f113,plain,
    ( spl6_6
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f118,plain,
    ( spl6_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f128,plain,
    ( spl6_9
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f133,plain,
    ( spl6_10
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f138,plain,
    ( spl6_11
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f143,plain,
    ( spl6_12
  <=> l1_waybel_9(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f272,plain,
    ( spl6_27
  <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f335,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))))
    | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | spl6_27
    | ~ spl6_29 ),
    inference(resolution,[],[f327,f314])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))
        | sK1 = k2_yellow_0(sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | spl6_27 ),
    inference(subsumption_resolution,[],[f326,f177])).

fof(f326,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0))
        | ~ m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,sK1)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | sK1 = k2_yellow_0(sK0,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_18
    | spl6_27 ),
    inference(resolution,[],[f310,f213])).

fof(f310,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | spl6_27 ),
    inference(subsumption_resolution,[],[f309,f177])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)
        | r1_orders_2(sK0,X0,sK1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | spl6_27 ),
    inference(resolution,[],[f300,f172])).

fof(f300,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | spl6_27 ),
    inference(subsumption_resolution,[],[f299,f150])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | spl6_27 ),
    inference(subsumption_resolution,[],[f298,f90])).

fof(f90,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f298,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | spl6_27 ),
    inference(subsumption_resolution,[],[f297,f95])).

fof(f95,plain,
    ( v4_orders_2(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK2)
        | v2_struct_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | spl6_27 ),
    inference(resolution,[],[f285,f100])).

fof(f100,plain,
    ( v7_waybel_0(sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f285,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | spl6_27 ),
    inference(subsumption_resolution,[],[f284,f105])).

fof(f105,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f284,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | spl6_27 ),
    inference(subsumption_resolution,[],[f283,f145])).

fof(f145,plain,
    ( l1_waybel_9(sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f283,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_27 ),
    inference(subsumption_resolution,[],[f282,f140])).

fof(f140,plain,
    ( v1_compts_1(sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f282,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_27 ),
    inference(subsumption_resolution,[],[f281,f135])).

fof(f135,plain,
    ( v2_lattice3(sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f281,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_27 ),
    inference(subsumption_resolution,[],[f280,f130])).

fof(f130,plain,
    ( v1_lattice3(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f280,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_27 ),
    inference(subsumption_resolution,[],[f279,f125])).

fof(f279,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_27 ),
    inference(subsumption_resolution,[],[f278,f120])).

fof(f120,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f278,plain,
    ( ! [X2,X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_27 ),
    inference(subsumption_resolution,[],[f277,f115])).

fof(f115,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f277,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl6_5
    | spl6_27 ),
    inference(subsumption_resolution,[],[f276,f110])).

fof(f110,plain,
    ( v8_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f276,plain,
    ( ! [X2,X0,X1] :
        ( ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2)
        | r1_orders_2(sK0,X2,X1) )
    | spl6_27 ),
    inference(resolution,[],[f274,f85])).

fof(f85,plain,(
    ! [X0,X5,X3,X1] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r1_orders_2(X0,X5,X3) ) ),
    inference(duplicate_literal_removal,[],[f79])).

% (19575)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f79,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r1_orders_2(X0,X5,X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | X2 != X3
      | m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r1_orders_2(X0,X5,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X3)
                      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
                         => r1_orders_2(X0,X5,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4)
                         => r1_orders_2(X0,X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l52_waybel_9)).

fof(f274,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f272])).

fof(f338,plain,
    ( ~ spl6_17
    | spl6_32 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl6_17
    | spl6_32 ),
    inference(subsumption_resolution,[],[f336,f182])).

fof(f182,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_17
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f336,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_32 ),
    inference(resolution,[],[f333,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f333,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_32 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl6_32
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f334,plain,
    ( ~ spl6_32
    | ~ spl6_13
    | spl6_30 ),
    inference(avatar_split_clause,[],[f329,f318,f148,f331])).

fof(f329,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl6_13
    | spl6_30 ),
    inference(subsumption_resolution,[],[f328,f150])).

fof(f328,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | ~ l1_struct_0(sK0)
    | spl6_30 ),
    inference(resolution,[],[f320,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f320,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f318])).

fof(f315,plain,
    ( spl6_29
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_26 ),
    inference(avatar_split_clause,[],[f308,f256,f175,f170,f153,f148,f143,f138,f133,f128,f123,f118,f113,f108,f103,f98,f93,f88,f312])).

fof(f153,plain,
    ( spl6_14
  <=> v11_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f256,plain,
    ( spl6_26
  <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f308,plain,
    ( r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16
    | spl6_26 ),
    inference(subsumption_resolution,[],[f307,f177])).

fof(f307,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_26 ),
    inference(resolution,[],[f291,f172])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_26 ),
    inference(subsumption_resolution,[],[f290,f90])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK2)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_26 ),
    inference(subsumption_resolution,[],[f289,f150])).

fof(f289,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK2)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | spl6_26 ),
    inference(subsumption_resolution,[],[f288,f100])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK2)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | spl6_26 ),
    inference(subsumption_resolution,[],[f287,f95])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK2)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14
    | spl6_26 ),
    inference(resolution,[],[f270,f155])).

fof(f155,plain,
    ( v11_waybel_0(sK2,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ v11_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(X0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | spl6_26 ),
    inference(subsumption_resolution,[],[f269,f105])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v11_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | spl6_26 ),
    inference(subsumption_resolution,[],[f268,f145])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v11_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_26 ),
    inference(subsumption_resolution,[],[f267,f140])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v11_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_26 ),
    inference(subsumption_resolution,[],[f266,f135])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v11_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_26 ),
    inference(subsumption_resolution,[],[f265,f130])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v11_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_26 ),
    inference(subsumption_resolution,[],[f264,f125])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v11_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_26 ),
    inference(subsumption_resolution,[],[f263,f120])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v11_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | ~ spl6_6
    | spl6_26 ),
    inference(subsumption_resolution,[],[f262,f115])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v11_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | ~ spl6_5
    | spl6_26 ),
    inference(subsumption_resolution,[],[f261,f110])).

fof(f261,plain,
    ( ! [X0,X1] :
        ( ~ v8_pre_topc(sK0)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ v11_waybel_0(X0,sK0)
        | ~ r3_waybel_9(sK0,X0,X1)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1) )
    | spl6_26 ),
    inference(resolution,[],[f258,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v11_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ v11_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | X2 != X3
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ v11_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ v11_waybel_0(X1,X0)
                  | ? [X4] :
                      ( ~ v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_waybel_9(X0)
      | ~ v1_compts_1(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r3_waybel_9(X0,X1,X2)
                      & v11_waybel_0(X1,X0)
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) )
                      & X2 = X3 )
                   => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_waybel_9)).

fof(f258,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f256])).

fof(f296,plain,
    ( spl6_28
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f286,f197,f180,f148,f293])).

fof(f293,plain,
    ( spl6_28
  <=> k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f197,plain,
    ( spl6_20
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_yellow_2(sK0,X1) = k2_yellow_0(sK0,k2_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f286,plain,
    ( k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(resolution,[],[f237,f150])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK0)
        | k5_yellow_2(sK0,u1_waybel_0(sK0,X0)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,X0))) )
    | ~ spl6_17
    | ~ spl6_20 ),
    inference(resolution,[],[f226,f182])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | k5_yellow_2(sK0,u1_waybel_0(X1,X0)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(X1,X0)))
        | ~ l1_waybel_0(X0,X1) )
    | ~ spl6_20 ),
    inference(resolution,[],[f214,f54])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | ~ l1_waybel_0(X1,X0)
        | k5_yellow_2(sK0,u1_waybel_0(X0,X1)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(X0,X1))) )
    | ~ spl6_20 ),
    inference(resolution,[],[f210,f74])).

fof(f210,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k5_yellow_2(sK0,X0) = k2_yellow_0(sK0,k2_relat_1(X0)) )
    | ~ spl6_20 ),
    inference(resolution,[],[f198,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f198,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_yellow_2(sK0,X1) = k2_yellow_0(sK0,k2_relat_1(X1)) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f275,plain,
    ( ~ spl6_27
    | spl6_24 ),
    inference(avatar_split_clause,[],[f260,f248,f272])).

fof(f248,plain,
    ( spl6_24
  <=> v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f260,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl6_24 ),
    inference(resolution,[],[f250,f36])).

fof(f36,plain,(
    ! [X3] :
      ( v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v11_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_waybel_9(X0,X2) != X1
              & r3_waybel_9(X0,X2,X1)
              & v11_waybel_0(X2,X0)
              & ! [X3] :
                  ( v5_pre_topc(k4_waybel_1(X0,X3),X0,X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_waybel_9(X0)
      & v1_compts_1(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_waybel_9(X0)
          & v1_compts_1(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( ( r3_waybel_9(X0,X2,X1)
                    & v11_waybel_0(X2,X0)
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
                 => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_waybel_9(X0)
        & v1_compts_1(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( ( r3_waybel_9(X0,X2,X1)
                  & v11_waybel_0(X2,X0)
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) ) )
               => k1_waybel_9(X0,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_9)).

fof(f250,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f248])).

fof(f259,plain,
    ( ~ spl6_26
    | spl6_22 ),
    inference(avatar_split_clause,[],[f246,f239,f256])).

fof(f239,plain,
    ( spl6_22
  <=> v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f246,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | spl6_22 ),
    inference(resolution,[],[f241,f36])).

fof(f241,plain,
    ( ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f239])).

fof(f254,plain,
    ( ~ spl6_24
    | spl6_25
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f236,f148,f143,f138,f133,f128,f123,f118,f113,f108,f103,f98,f93,f88,f252,f248])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f235,f150])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f234,f105])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f233,f145])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f232,f110])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( ~ v8_pre_topc(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f231,f135])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( ~ v2_lattice3(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f230,f130])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f229,f125])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f228,f120])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f227,f115])).

fof(f227,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v8_pre_topc(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1)
        | r1_orders_2(sK0,X1,X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(resolution,[],[f160,f140])).

fof(f160,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_compts_1(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v8_pre_topc(X0)
        | ~ l1_waybel_9(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X2)
        | r1_orders_2(X0,X2,X1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f159,f95])).

fof(f159,plain,
    ( ! [X2,X0,X1] :
        ( ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | ~ v4_orders_2(sK2)
        | ~ v2_pre_topc(X0)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X2)
        | r1_orders_2(X0,X2,X1) )
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f157,f90])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( ~ v8_pre_topc(X0)
        | ~ v3_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v5_orders_2(X0)
        | ~ v1_lattice3(X0)
        | ~ v2_lattice3(X0)
        | ~ v1_compts_1(X0)
        | ~ l1_waybel_9(X0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v2_pre_topc(X0)
        | ~ l1_waybel_0(sK2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
        | ~ r3_waybel_9(X0,sK2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X2)
        | r1_orders_2(X0,X2,X1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f100,f86])).

fof(f86,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r1_orders_2(X0,X5,X3) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r1_orders_2(X0,X5,X3) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | X2 != X3
      | ~ v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)
      | r1_orders_2(X0,X5,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f245,plain,
    ( ~ spl6_22
    | spl6_23
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f225,f153,f148,f143,f138,f133,f128,f123,f118,f113,f108,f103,f98,f93,f88,f243,f239])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f224,f110])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f223,f150])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f222,f105])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f221,f145])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f220,f140])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f219,f135])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f218,f130])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f217,f125])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f216,f120])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f215,f115])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v1_compts_1(sK0)
        | ~ l1_waybel_9(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)
        | ~ v8_pre_topc(sK0)
        | ~ r3_waybel_9(sK0,sK2,X0)
        | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_14 ),
    inference(resolution,[],[f162,f155])).

fof(f162,plain,
    ( ! [X4,X3] :
        ( ~ v11_waybel_0(sK2,X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ v1_compts_1(X3)
        | ~ l1_waybel_9(X3)
        | ~ v2_pre_topc(X3)
        | ~ l1_waybel_0(sK2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ v5_pre_topc(k4_waybel_1(X3,sK3(X3)),X3,X3)
        | ~ v8_pre_topc(X3)
        | ~ r3_waybel_9(X3,sK2,X4)
        | r1_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f161,f95])).

fof(f161,plain,
    ( ! [X4,X3] :
        ( ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ v1_compts_1(X3)
        | ~ l1_waybel_9(X3)
        | ~ v4_orders_2(sK2)
        | ~ v2_pre_topc(X3)
        | ~ l1_waybel_0(sK2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ v5_pre_topc(k4_waybel_1(X3,sK3(X3)),X3,X3)
        | ~ v11_waybel_0(sK2,X3)
        | ~ r3_waybel_9(X3,sK2,X4)
        | r1_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4) )
    | spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f158,f90])).

fof(f158,plain,
    ( ! [X4,X3] :
        ( ~ v8_pre_topc(X3)
        | ~ v3_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v5_orders_2(X3)
        | ~ v1_lattice3(X3)
        | ~ v2_lattice3(X3)
        | ~ v1_compts_1(X3)
        | ~ l1_waybel_9(X3)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v2_pre_topc(X3)
        | ~ l1_waybel_0(sK2,X3)
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ v5_pre_topc(k4_waybel_1(X3,sK3(X3)),X3,X3)
        | ~ v11_waybel_0(sK2,X3)
        | ~ r3_waybel_9(X3,sK2,X4)
        | r1_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4) )
    | ~ spl6_3 ),
    inference(resolution,[],[f100,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ v11_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ v11_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X3)
      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v8_pre_topc(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_compts_1(X0)
      | ~ l1_waybel_9(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | X2 != X3
      | ~ v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0)
      | ~ v11_waybel_0(X1,X0)
      | ~ r3_waybel_9(X0,X1,X2)
      | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f208,plain,
    ( ~ spl6_9
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f206,f187])).

fof(f206,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f205,f130])).

fof(f205,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_21 ),
    inference(resolution,[],[f202,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f202,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f200])).

fof(f203,plain,
    ( spl6_20
    | spl6_21
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f195,f185,f200,f197])).

fof(f195,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ v1_relat_1(X1)
        | k5_yellow_2(sK0,X1) = k2_yellow_0(sK0,k2_relat_1(X1)) )
    | ~ spl6_18 ),
    inference(resolution,[],[f187,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_relat_1(X1)
      | k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_yellow_2)).

fof(f193,plain,(
    ~ spl6_19 ),
    inference(avatar_split_clause,[],[f43,f190])).

fof(f43,plain,(
    sK1 != k1_waybel_9(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f188,plain,
    ( spl6_18
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f168,f143,f185])).

fof(f168,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f145,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & l1_pre_topc(X0) )
      | ~ l1_waybel_9(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_waybel_9(X0)
     => ( l1_orders_2(X0)
        & l1_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

fof(f183,plain,
    ( spl6_17
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f167,f143,f180])).

fof(f167,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f145,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_waybel_9(X0)
      | l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f178,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f44,f175])).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f173,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f42,f170])).

fof(f42,plain,(
    r3_waybel_9(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f156,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f41,f153])).

fof(f41,plain,(
    v11_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f151,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f40,f148])).

fof(f40,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f146,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f53,f143])).

fof(f53,plain,(
    l1_waybel_9(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f141,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f52,f138])).

fof(f52,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f136,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f51,f133])).

fof(f51,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f50,f128])).

fof(f50,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f126,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f49,f123])).

fof(f49,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f121,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f48,f118])).

fof(f48,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f47,f113])).

fof(f47,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f111,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f46,f108])).

fof(f46,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f106,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f45,f103])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f39,f98])).

fof(f39,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f38,f93])).

fof(f38,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f37,f88])).

fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (19587)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (19578)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (19577)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (19585)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (19577)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f513,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f151,f156,f173,f178,f183,f188,f193,f203,f208,f245,f254,f259,f275,f296,f315,f334,f338,f407,f427,f438,f446,f457,f468,f488,f511])).
% 0.21/0.49  fof(f511,plain,(
% 0.21/0.49    ~spl6_8 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_25 | ~spl6_29 | spl6_40 | ~spl6_42),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f510])).
% 0.21/0.49  fof(f510,plain,(
% 0.21/0.49    $false | (~spl6_8 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_25 | ~spl6_29 | spl6_40 | ~spl6_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f509,f177])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f175])).
% 0.21/0.49  % (19585)Refutation not found, incomplete strategy% (19585)------------------------------
% 0.21/0.49  % (19585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl6_16 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.49  % (19585)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19585)Memory used [KB]: 10874
% 0.21/0.49  fof(f509,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_8 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_25 | ~spl6_29 | spl6_40 | ~spl6_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f508,f397])).
% 0.21/0.49  % (19585)Time elapsed: 0.075 s
% 0.21/0.49  % (19585)------------------------------
% 0.21/0.49  % (19585)------------------------------
% 0.21/0.49  fof(f397,plain,(
% 0.21/0.49    sK1 != k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | spl6_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f396])).
% 0.21/0.49  fof(f396,plain,(
% 0.21/0.49    spl6_40 <=> sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.49  fof(f508,plain,(
% 0.21/0.49    sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_8 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_25 | ~spl6_29 | ~spl6_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f507,f314])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~spl6_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f312])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    spl6_29 <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.49  fof(f507,plain,(
% 0.21/0.49    ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_8 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_25 | ~spl6_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f506,f405])).
% 0.21/0.49  fof(f405,plain,(
% 0.21/0.49    m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | ~spl6_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f404])).
% 0.21/0.49  fof(f404,plain,(
% 0.21/0.49    spl6_42 <=> m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.49  fof(f506,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_8 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_25)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f504])).
% 0.21/0.49  fof(f504,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | (~spl6_8 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_25)),
% 0.21/0.49    inference(resolution,[],[f498,f211])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ( ! [X4,X5] : (r1_lattice3(sK0,X5,sK5(sK0,X4,X5)) | ~r1_lattice3(sK0,X5,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_yellow_0(sK0,X5) = X4) ) | (~spl6_8 | ~spl6_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f165,f187])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    l1_orders_2(sK0) | ~spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl6_18 <=> l1_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~l1_orders_2(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X5,X4) | r1_lattice3(sK0,X5,sK5(sK0,X4,X5)) | k2_yellow_0(sK0,X5) = X4) ) | ~spl6_8),
% 0.21/0.49    inference(resolution,[],[f125,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | r1_lattice3(X0,X2,sK5(X0,X1,X2)) | k2_yellow_0(X0,X2) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.21/0.49    inference(rectify,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    v5_orders_2(sK0) | ~spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl6_8 <=> v5_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f498,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) | ~m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,sK1) | sK1 = k2_yellow_0(sK0,X0)) ) | (~spl6_8 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f497,f177])).
% 0.21/0.49  fof(f497,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) | ~r1_lattice3(sK0,X0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_yellow_0(sK0,X0)) ) | (~spl6_8 | ~spl6_15 | ~spl6_16 | ~spl6_18 | ~spl6_25)),
% 0.21/0.49    inference(resolution,[],[f491,f213])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ( ! [X6,X7] : (~r1_orders_2(sK0,sK5(sK0,X6,X7),X6) | ~r1_lattice3(sK0,X7,X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | k2_yellow_0(sK0,X7) = X6) ) | (~spl6_8 | ~spl6_18)),
% 0.21/0.49    inference(subsumption_resolution,[],[f166,f187])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ( ! [X6,X7] : (~l1_orders_2(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X7,X6) | ~r1_orders_2(sK0,sK5(sK0,X6,X7),X6) | k2_yellow_0(sK0,X7) = X6) ) | ~spl6_8),
% 0.21/0.49    inference(resolution,[],[f125,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~r1_orders_2(X0,sK5(X0,X1,X2),X1) | k2_yellow_0(X0,X2) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f491,plain,(
% 0.21/0.49    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (~spl6_15 | ~spl6_16 | ~spl6_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f490,f177])).
% 0.21/0.49  fof(f490,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(sK1,u1_struct_0(sK0))) ) | (~spl6_15 | ~spl6_25)),
% 0.21/0.49    inference(resolution,[],[f253,f172])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    r3_waybel_9(sK0,sK2,sK1) | ~spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    spl6_15 <=> r3_waybel_9(sK0,sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,X0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f252])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    spl6_25 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK0,X1,X0) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | ~r3_waybel_9(sK0,sK2,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.49  fof(f488,plain,(
% 0.21/0.49    ~spl6_8 | ~spl6_16 | ~spl6_18 | ~spl6_29 | spl6_40 | spl6_41),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f487])).
% 0.21/0.49  fof(f487,plain,(
% 0.21/0.49    $false | (~spl6_8 | ~spl6_16 | ~spl6_18 | ~spl6_29 | spl6_40 | spl6_41)),
% 0.21/0.49    inference(subsumption_resolution,[],[f486,f397])).
% 0.21/0.49  fof(f486,plain,(
% 0.21/0.49    sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | (~spl6_8 | ~spl6_16 | ~spl6_18 | ~spl6_29 | spl6_41)),
% 0.21/0.49    inference(subsumption_resolution,[],[f485,f177])).
% 0.21/0.49  fof(f485,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | (~spl6_8 | ~spl6_18 | ~spl6_29 | spl6_41)),
% 0.21/0.49    inference(subsumption_resolution,[],[f483,f314])).
% 0.21/0.49  fof(f483,plain,(
% 0.21/0.49    ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | (~spl6_8 | ~spl6_18 | spl6_41)),
% 0.21/0.49    inference(resolution,[],[f402,f211])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))) | spl6_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f400])).
% 0.21/0.49  fof(f400,plain,(
% 0.21/0.49    spl6_41 <=> r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.49  fof(f468,plain,(
% 0.21/0.49    ~spl6_13 | ~spl6_18 | spl6_19 | spl6_21 | ~spl6_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f467])).
% 0.21/0.49  fof(f467,plain,(
% 0.21/0.49    $false | (~spl6_13 | ~spl6_18 | spl6_19 | spl6_21 | ~spl6_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f466,f150])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    l1_waybel_0(sK2,sK0) | ~spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl6_13 <=> l1_waybel_0(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f466,plain,(
% 0.21/0.49    ~l1_waybel_0(sK2,sK0) | (~spl6_18 | spl6_19 | spl6_21 | ~spl6_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f462,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    sK1 != k1_waybel_9(sK0,sK2) | spl6_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    spl6_19 <=> sK1 = k1_waybel_9(sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.49  fof(f462,plain,(
% 0.21/0.49    sK1 = k1_waybel_9(sK0,sK2) | ~l1_waybel_0(sK2,sK0) | (~spl6_18 | spl6_21 | ~spl6_39)),
% 0.21/0.49    inference(superposition,[],[f212,f378])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) | ~spl6_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f376])).
% 0.21/0.49  fof(f376,plain,(
% 0.21/0.49    spl6_39 <=> sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ( ! [X0] : (k1_waybel_9(sK0,X0) = k5_yellow_2(sK0,u1_waybel_0(sK0,X0)) | ~l1_waybel_0(X0,sK0)) ) | (~spl6_18 | spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f194,f201])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl6_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f200])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    spl6_21 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~l1_waybel_0(X0,sK0) | k1_waybel_9(sK0,X0) = k5_yellow_2(sK0,u1_waybel_0(sK0,X0))) ) | ~spl6_18),
% 0.21/0.49    inference(resolution,[],[f187,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (l1_waybel_0(X1,X0) => k1_waybel_9(X0,X1) = k5_yellow_2(X0,u1_waybel_0(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_9)).
% 0.21/0.49  fof(f457,plain,(
% 0.21/0.49    sK1 != k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) != k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | sK1 = k5_yellow_2(sK0,u1_waybel_0(sK0,sK2))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f446,plain,(
% 0.21/0.49    ~spl6_30 | ~spl6_40 | spl6_43),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f445])).
% 0.21/0.49  fof(f445,plain,(
% 0.21/0.49    $false | (~spl6_30 | ~spl6_40 | spl6_43)),
% 0.21/0.49    inference(subsumption_resolution,[],[f444,f319])).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f318])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    spl6_30 <=> m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.49  fof(f444,plain,(
% 0.21/0.49    ~m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | (~spl6_40 | spl6_43)),
% 0.21/0.49    inference(subsumption_resolution,[],[f441,f413])).
% 0.21/0.49  fof(f413,plain,(
% 0.21/0.49    sK1 != k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | spl6_43),
% 0.21/0.49    inference(avatar_component_clause,[],[f411])).
% 0.21/0.49  fof(f411,plain,(
% 0.21/0.49    spl6_43 <=> sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.49  fof(f441,plain,(
% 0.21/0.49    sK1 = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | ~m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | ~spl6_40),
% 0.21/0.49    inference(superposition,[],[f398,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f398,plain,(
% 0.21/0.49    sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | ~spl6_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f396])).
% 0.21/0.49  fof(f438,plain,(
% 0.21/0.49    spl6_29 | ~spl6_15 | ~spl6_16 | ~spl6_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f433,f243,f175,f170,f312])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    spl6_23 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~r3_waybel_9(sK0,sK2,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.49  fof(f433,plain,(
% 0.21/0.49    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (~spl6_15 | ~spl6_16 | ~spl6_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f432,f177])).
% 0.21/0.49  fof(f432,plain,(
% 0.21/0.49    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_15 | ~spl6_23)),
% 0.21/0.49    inference(resolution,[],[f244,f172])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f243])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    ~spl6_8 | ~spl6_16 | ~spl6_18 | ~spl6_29 | spl6_40 | spl6_42),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f426])).
% 0.21/0.49  fof(f426,plain,(
% 0.21/0.49    $false | (~spl6_8 | ~spl6_16 | ~spl6_18 | ~spl6_29 | spl6_40 | spl6_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f425,f397])).
% 0.21/0.49  fof(f425,plain,(
% 0.21/0.49    sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | (~spl6_8 | ~spl6_16 | ~spl6_18 | ~spl6_29 | spl6_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f424,f125])).
% 0.21/0.49  fof(f424,plain,(
% 0.21/0.49    ~v5_orders_2(sK0) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | (~spl6_16 | ~spl6_18 | ~spl6_29 | spl6_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f423,f314])).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_orders_2(sK0) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | (~spl6_16 | ~spl6_18 | spl6_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f422,f177])).
% 0.21/0.49  fof(f422,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_orders_2(sK0) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | (~spl6_18 | spl6_42)),
% 0.21/0.49    inference(subsumption_resolution,[],[f416,f187])).
% 0.21/0.49  fof(f416,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | ~v5_orders_2(sK0) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | spl6_42),
% 0.21/0.49    inference(resolution,[],[f406,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X1) | ~v5_orders_2(X0) | k2_yellow_0(X0,X2) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f406,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | spl6_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f404])).
% 0.21/0.49  fof(f407,plain,(
% 0.21/0.49    spl6_40 | ~spl6_41 | ~spl6_42 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_18 | spl6_27 | ~spl6_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f335,f312,f272,f185,f175,f170,f148,f143,f138,f133,f128,f123,f118,f113,f108,f103,f98,f93,f88,f404,f400,f396])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl6_1 <=> v2_struct_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl6_2 <=> v4_orders_2(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl6_3 <=> v7_waybel_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl6_4 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl6_5 <=> v8_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl6_6 <=> v3_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl6_7 <=> v4_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl6_9 <=> v1_lattice3(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl6_10 <=> v2_lattice3(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    spl6_11 <=> v1_compts_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl6_12 <=> l1_waybel_9(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    spl6_27 <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.49  fof(f335,plain,(
% 0.21/0.49    ~m1_subset_1(sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)))) | sK1 = k2_yellow_0(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_18 | spl6_27 | ~spl6_29)),
% 0.21/0.49    inference(resolution,[],[f327,f314])).
% 0.21/0.49  fof(f327,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_lattice3(sK0,X0,sK1) | ~m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) | sK1 = k2_yellow_0(sK0,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_18 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f326,f177])).
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK5(sK0,sK1,X0)) | ~m1_subset_1(sK5(sK0,sK1,X0),u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_yellow_0(sK0,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_18 | spl6_27)),
% 0.21/0.49    inference(resolution,[],[f310,f213])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f309,f177])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0) | r1_orders_2(sK0,X0,sK1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | spl6_27)),
% 0.21/0.49    inference(resolution,[],[f300,f172])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f299,f150])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f298,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~v2_struct_0(sK2) | spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f297,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    v4_orders_2(sK2) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_27)),
% 0.21/0.49    inference(resolution,[],[f285,f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    v7_waybel_0(sK2) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f98])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f284,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    v2_pre_topc(sK0) | ~spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f103])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f283,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    l1_waybel_9(sK0) | ~spl6_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f282,f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    v1_compts_1(sK0) | ~spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f138])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f281,f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    v2_lattice3(sK0) | ~spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f133])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f280,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    v1_lattice3(sK0) | ~spl6_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f279,f125])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f278,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    v4_orders_2(sK0) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f118])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | (~spl6_5 | ~spl6_6 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f277,f115])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    v3_orders_2(sK0) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | (~spl6_5 | spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f276,f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    v8_pre_topc(sK0) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X2) | r1_orders_2(sK0,X2,X1)) ) | spl6_27),
% 0.21/0.49    inference(resolution,[],[f274,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0,X5,X3,X1] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r1_orders_2(X0,X5,X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f79])).
% 0.21/0.49  % (19575)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r1_orders_2(X0,X5,X3)) )),
% 0.21/0.49    inference(equality_resolution,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | X2 != X3 | m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r1_orders_2(X0,X5,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X5] : ((r1_orders_2(X0,X5,X3) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5)) | ~m1_subset_1(X5,u1_struct_0(X0))) | (~r3_waybel_9(X0,X1,X2) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) => r1_orders_2(X0,X5,X3))))))))),
% 0.21/0.49    inference(rectify,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X4) => r1_orders_2(X0,X4,X3))))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l52_waybel_9)).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | spl6_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f272])).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    ~spl6_17 | spl6_32),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f337])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    $false | (~spl6_17 | spl6_32)),
% 0.21/0.49    inference(subsumption_resolution,[],[f336,f182])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl6_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f180])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl6_17 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | spl6_32),
% 0.21/0.49    inference(resolution,[],[f333,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f333,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | spl6_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f331])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    spl6_32 <=> l1_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    ~spl6_32 | ~spl6_13 | spl6_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f329,f318,f148,f331])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    ~l1_struct_0(sK0) | (~spl6_13 | spl6_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f328,f150])).
% 0.21/0.49  fof(f328,plain,(
% 0.21/0.49    ~l1_waybel_0(sK2,sK0) | ~l1_struct_0(sK0) | spl6_30),
% 0.21/0.49    inference(resolution,[],[f320,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    ~m1_subset_1(u1_waybel_0(sK0,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) | spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f318])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    spl6_29 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f308,f256,f175,f170,f153,f148,f143,f138,f133,f128,f123,f118,f113,f108,f103,f98,f93,f88,f312])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    spl6_14 <=> v11_waybel_0(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    spl6_26 <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f307,f177])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_26)),
% 0.21/0.49    inference(resolution,[],[f291,f172])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ( ! [X0] : (~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f290,f90])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK2) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f289,f150])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK2) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f288,f100])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ( ! [X0] : (~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK2) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f287,f95])).
% 0.21/0.49  fof(f287,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK2) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | spl6_26)),
% 0.21/0.49    inference(resolution,[],[f270,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    v11_waybel_0(sK2,sK0) | ~spl6_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f153])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v11_waybel_0(X0,sK0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(X0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f269,f105])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v11_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f268,f145])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v11_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f267,f140])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v11_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f266,f135])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v11_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f265,f130])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v11_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f264,f125])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v11_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | ~spl6_7 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f263,f120])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v11_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | ~spl6_6 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f262,f115])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v11_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | (~spl6_5 | spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f261,f110])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v8_pre_topc(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v11_waybel_0(X0,sK0) | ~r3_waybel_9(sK0,X0,X1) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(X0),u1_struct_0(sK0),u1_waybel_0(sK0,X0)),X1)) ) | spl6_26),
% 0.21/0.49    inference(resolution,[],[f258,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v11_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X3) | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~v11_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X3) | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.49    inference(equality_resolution,[],[f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | X2 != X3 | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~v11_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X2) | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | ~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3) | (~r3_waybel_9(X0,X1,X2) | ~v11_waybel_0(X1,X0) | ? [X4] : (~v5_pre_topc(k4_waybel_1(X0,X4),X0,X0) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_waybel_9(X0) | ~v1_compts_1(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~v8_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r3_waybel_9(X0,X1,X2) & v11_waybel_0(X1,X0) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X4),X0,X0)) & X2 = X3) => r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_waybel_9)).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | spl6_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f256])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    spl6_28 | ~spl6_13 | ~spl6_17 | ~spl6_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f286,f197,f180,f148,f293])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    spl6_28 <=> k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl6_20 <=> ! [X1] : (~v1_relat_1(X1) | k5_yellow_2(sK0,X1) = k2_yellow_0(sK0,k2_relat_1(X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    k5_yellow_2(sK0,u1_waybel_0(sK0,sK2)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,sK2))) | (~spl6_13 | ~spl6_17 | ~spl6_20)),
% 0.21/0.49    inference(resolution,[],[f237,f150])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(X0,sK0) | k5_yellow_2(sK0,u1_waybel_0(sK0,X0)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(sK0,X0)))) ) | (~spl6_17 | ~spl6_20)),
% 0.21/0.49    inference(resolution,[],[f226,f182])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_pre_topc(X1) | k5_yellow_2(sK0,u1_waybel_0(X1,X0)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(X1,X0))) | ~l1_waybel_0(X0,X1)) ) | ~spl6_20),
% 0.21/0.49    inference(resolution,[],[f214,f54])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | k5_yellow_2(sK0,u1_waybel_0(X0,X1)) = k2_yellow_0(sK0,k2_relat_1(u1_waybel_0(X0,X1)))) ) | ~spl6_20),
% 0.21/0.49    inference(resolution,[],[f210,f74])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_yellow_2(sK0,X0) = k2_yellow_0(sK0,k2_relat_1(X0))) ) | ~spl6_20),
% 0.21/0.49    inference(resolution,[],[f198,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_relat_1(X1) | k5_yellow_2(sK0,X1) = k2_yellow_0(sK0,k2_relat_1(X1))) ) | ~spl6_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f197])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    ~spl6_27 | spl6_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f260,f248,f272])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    spl6_24 <=> v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | spl6_24),
% 0.21/0.49    inference(resolution,[],[f250,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X3] : (v5_pre_topc(k4_waybel_1(sK0,X3),sK0,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k1_waybel_9(X0,X2) != X1 & r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((k1_waybel_9(X0,X2) != X1 & (r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (v5_pre_topc(k4_waybel_1(X0,X3),X0,X0) | ~m1_subset_1(X3,u1_struct_0(X0))))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_waybel_9(X0) & v1_compts_1(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & v8_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((r3_waybel_9(X0,X2,X1) & v11_waybel_0(X2,X0) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => v5_pre_topc(k4_waybel_1(X0,X3),X0,X0))) => k1_waybel_9(X0,X2) = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_9)).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | spl6_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f248])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    ~spl6_26 | spl6_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f246,f239,f256])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    spl6_22 <=> v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | spl6_22),
% 0.21/0.49    inference(resolution,[],[f241,f36])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | spl6_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f239])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ~spl6_24 | spl6_25 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f236,f148,f143,f138,f133,f128,f123,f118,f113,f108,f103,f98,f93,f88,f252,f248])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f235,f150])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f234,f105])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f233,f145])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f232,f110])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v8_pre_topc(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f231,f135])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_lattice3(sK0) | ~v8_pre_topc(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f230,f130])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v8_pre_topc(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f229,f125])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v8_pre_topc(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f228,f120])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v8_pre_topc(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f227,f115])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v8_pre_topc(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK4(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X1) | r1_orders_2(sK0,X1,X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_11)),
% 0.21/0.49    inference(resolution,[],[f160,f140])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_compts_1(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v8_pre_topc(X0) | ~l1_waybel_9(X0) | ~v2_pre_topc(X0) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~r3_waybel_9(X0,sK2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X2) | r1_orders_2(X0,X2,X1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f159,f95])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | ~v4_orders_2(sK2) | ~v2_pre_topc(X0) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~r3_waybel_9(X0,sK2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X2) | r1_orders_2(X0,X2,X1)) ) | (spl6_1 | ~spl6_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f157,f90])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v2_pre_topc(X0) | ~l1_waybel_0(sK2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~r3_waybel_9(X0,sK2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X0),u1_waybel_0(X0,sK2)),X2) | r1_orders_2(X0,X2,X1)) ) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f100,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X0,X5,X3,X1] : (~v7_waybel_0(X1) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v2_pre_topc(X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r1_orders_2(X0,X5,X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~r3_waybel_9(X0,X1,X3) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r1_orders_2(X0,X5,X3)) )),
% 0.21/0.49    inference(equality_resolution,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | X2 != X3 | ~v5_pre_topc(k4_waybel_1(X0,sK4(X0)),X0,X0) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X5) | r1_orders_2(X0,X5,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    ~spl6_22 | spl6_23 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f225,f153,f148,f143,f138,f133,f128,f123,f118,f113,f108,f103,f98,f93,f88,f243,f239])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f110])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f223,f150])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f222,f105])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f221,f145])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f220,f140])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f219,f135])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f218,f130])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f217,f125])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ( ! [X0] : (~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f216,f120])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_6 | ~spl6_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f215,f115])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~v1_lattice3(sK0) | ~v2_lattice3(sK0) | ~v1_compts_1(sK0) | ~l1_waybel_9(sK0) | ~v2_pre_topc(sK0) | ~l1_waybel_0(sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_pre_topc(k4_waybel_1(sK0,sK3(sK0)),sK0,sK0) | ~v8_pre_topc(sK0) | ~r3_waybel_9(sK0,sK2,X0) | r1_lattice3(sK0,k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)),X0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_14)),
% 0.21/0.49    inference(resolution,[],[f162,f155])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~v11_waybel_0(sK2,X3) | ~v3_orders_2(X3) | ~v4_orders_2(X3) | ~v5_orders_2(X3) | ~v1_lattice3(X3) | ~v2_lattice3(X3) | ~v1_compts_1(X3) | ~l1_waybel_9(X3) | ~v2_pre_topc(X3) | ~l1_waybel_0(sK2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~v5_pre_topc(k4_waybel_1(X3,sK3(X3)),X3,X3) | ~v8_pre_topc(X3) | ~r3_waybel_9(X3,sK2,X4) | r1_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4)) ) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f161,f95])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~v8_pre_topc(X3) | ~v3_orders_2(X3) | ~v4_orders_2(X3) | ~v5_orders_2(X3) | ~v1_lattice3(X3) | ~v2_lattice3(X3) | ~v1_compts_1(X3) | ~l1_waybel_9(X3) | ~v4_orders_2(sK2) | ~v2_pre_topc(X3) | ~l1_waybel_0(sK2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~v5_pre_topc(k4_waybel_1(X3,sK3(X3)),X3,X3) | ~v11_waybel_0(sK2,X3) | ~r3_waybel_9(X3,sK2,X4) | r1_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4)) ) | (spl6_1 | ~spl6_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f158,f90])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~v8_pre_topc(X3) | ~v3_orders_2(X3) | ~v4_orders_2(X3) | ~v5_orders_2(X3) | ~v1_lattice3(X3) | ~v2_lattice3(X3) | ~v1_compts_1(X3) | ~l1_waybel_9(X3) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v2_pre_topc(X3) | ~l1_waybel_0(sK2,X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~v5_pre_topc(k4_waybel_1(X3,sK3(X3)),X3,X3) | ~v11_waybel_0(sK2,X3) | ~r3_waybel_9(X3,sK2,X4) | r1_lattice3(X3,k2_relset_1(u1_struct_0(sK2),u1_struct_0(X3),u1_waybel_0(X3,sK2)),X4)) ) | ~spl6_3),
% 0.21/0.49    inference(resolution,[],[f100,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v7_waybel_0(X1) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v2_pre_topc(X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~v11_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X3) | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~v11_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X3) | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.49    inference(equality_resolution,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~v8_pre_topc(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~v1_lattice3(X0) | ~v2_lattice3(X0) | ~v1_compts_1(X0) | ~l1_waybel_9(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | X2 != X3 | ~v5_pre_topc(k4_waybel_1(X0,sK3(X0)),X0,X0) | ~v11_waybel_0(X1,X0) | ~r3_waybel_9(X0,X1,X2) | r1_lattice3(X0,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ~spl6_9 | ~spl6_18 | ~spl6_21),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f207])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    $false | (~spl6_9 | ~spl6_18 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f206,f187])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ~l1_orders_2(sK0) | (~spl6_9 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f205,f130])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl6_21),
% 0.21/0.49    inference(resolution,[],[f202,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~spl6_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f200])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    spl6_20 | spl6_21 | ~spl6_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f195,f185,f200,f197])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X1] : (v2_struct_0(sK0) | ~v1_relat_1(X1) | k5_yellow_2(sK0,X1) = k2_yellow_0(sK0,k2_relat_1(X1))) ) | ~spl6_18),
% 0.21/0.49    inference(resolution,[],[f187,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_orders_2(X0) | v2_struct_0(X0) | ~v1_relat_1(X1) | k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (v1_relat_1(X1) => k5_yellow_2(X0,X1) = k2_yellow_0(X0,k2_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_yellow_2)).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ~spl6_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f190])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    sK1 != k1_waybel_9(sK0,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    spl6_18 | ~spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f168,f143,f185])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    l1_orders_2(sK0) | ~spl6_12),
% 0.21/0.49    inference(resolution,[],[f145,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_9(X0) | l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & l1_pre_topc(X0)) | ~l1_waybel_9(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (l1_waybel_9(X0) => (l1_orders_2(X0) & l1_pre_topc(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    spl6_17 | ~spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f167,f143,f180])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl6_12),
% 0.21/0.49    inference(resolution,[],[f145,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_waybel_9(X0) | l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    spl6_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f175])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl6_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f170])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    r3_waybel_9(sK0,sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f153])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    v11_waybel_0(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl6_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f148])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    l1_waybel_0(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl6_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f53,f143])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    l1_waybel_9(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl6_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f138])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v1_compts_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f133])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    v2_lattice3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f128])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    v1_lattice3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl6_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f123])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    v5_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f118])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    v4_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f113])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v3_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f108])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    v8_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f103])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f98])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v7_waybel_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f93])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v4_orders_2(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f88])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ~v2_struct_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (19577)------------------------------
% 0.21/0.49  % (19577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19577)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (19577)Memory used [KB]: 11001
% 0.21/0.49  % (19577)Time elapsed: 0.071 s
% 0.21/0.49  % (19577)------------------------------
% 0.21/0.49  % (19577)------------------------------
% 0.21/0.49  % (19575)Refutation not found, incomplete strategy% (19575)------------------------------
% 0.21/0.49  % (19575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19575)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19575)Memory used [KB]: 10618
% 0.21/0.49  % (19575)Time elapsed: 0.070 s
% 0.21/0.49  % (19575)------------------------------
% 0.21/0.49  % (19575)------------------------------
% 0.21/0.49  % (19584)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (19572)Success in time 0.137 s
%------------------------------------------------------------------------------
