%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1543+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 599 expanded)
%              Number of leaves         :   46 ( 292 expanded)
%              Depth                    :   11
%              Number of atoms          : 1310 (4825 expanded)
%              Number of equality atoms :   13 (  95 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f81,f85,f89,f97,f104,f108,f129,f136,f155,f162,f171,f178,f207,f215,f225,f246,f251,f258,f260,f262,f269,f306,f312,f320,f326,f345,f347,f354,f357,f363,f368,f370])).

fof(f370,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | ~ spl8_18
    | ~ spl8_13
    | ~ spl8_48
    | spl8_52 ),
    inference(avatar_split_clause,[],[f369,f366,f340,f122,f148,f83,f87])).

fof(f87,plain,
    ( spl8_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f83,plain,
    ( spl8_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f148,plain,
    ( spl8_18
  <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f122,plain,
    ( spl8_13
  <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f340,plain,
    ( spl8_48
  <=> r2_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f366,plain,
    ( spl8_52
  <=> r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f369,plain,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_52 ),
    inference(resolution,[],[f367,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f60,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f12,f29])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
        & m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_0)).

fof(f367,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0)),sK3(sK0))
    | spl8_52 ),
    inference(avatar_component_clause,[],[f366])).

fof(f368,plain,
    ( ~ spl8_46
    | ~ spl8_52
    | ~ spl8_47
    | ~ spl8_8
    | spl8_49 ),
    inference(avatar_split_clause,[],[f364,f343,f95,f337,f366,f334])).

fof(f334,plain,
    ( spl8_46
  <=> r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f337,plain,
    ( spl8_47
  <=> m1_subset_1(k11_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f95,plain,
    ( spl8_8
  <=> ! [X0] :
        ( r1_orders_2(sK0,sK5(sK0,X0),sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3(sK0))
        | ~ r1_orders_2(sK0,X0,sK4(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f343,plain,
    ( spl8_49
  <=> r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0))),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f364,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0)),sK3(sK0))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0)),sK4(sK0))
    | ~ spl8_8
    | spl8_49 ),
    inference(resolution,[],[f344,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK5(sK0,X0),sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3(sK0))
        | ~ r1_orders_2(sK0,X0,sK4(sK0)) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f344,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0))),sK3(sK0))
    | spl8_49 ),
    inference(avatar_component_clause,[],[f343])).

fof(f363,plain,
    ( ~ spl8_6
    | ~ spl8_18
    | ~ spl8_13
    | spl8_47 ),
    inference(avatar_split_clause,[],[f362,f337,f122,f148,f83])).

fof(f362,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_47 ),
    inference(resolution,[],[f338,f58])).

fof(f338,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | spl8_47 ),
    inference(avatar_component_clause,[],[f337])).

fof(f357,plain,
    ( ~ spl8_13
    | ~ spl8_18
    | ~ spl8_5
    | spl8_48 ),
    inference(avatar_split_clause,[],[f355,f340,f79,f148,f122])).

fof(f79,plain,
    ( spl8_5
  <=> ! [X3,X4] :
        ( r2_yellow_0(sK0,k2_tarski(X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f355,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl8_5
    | spl8_48 ),
    inference(resolution,[],[f341,f80])).

fof(f80,plain,
    ( ! [X4,X3] :
        ( r2_yellow_0(sK0,k2_tarski(X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f341,plain,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | spl8_48 ),
    inference(avatar_component_clause,[],[f340])).

fof(f354,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | ~ spl8_18
    | ~ spl8_13
    | ~ spl8_48
    | spl8_46 ),
    inference(avatar_split_clause,[],[f353,f334,f340,f122,f148,f83,f87])).

fof(f353,plain,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_46 ),
    inference(resolution,[],[f335,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f61,f58])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f335,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0)),sK4(sK0))
    | spl8_46 ),
    inference(avatar_component_clause,[],[f334])).

fof(f347,plain,
    ( ~ spl8_6
    | spl8_1
    | spl8_13 ),
    inference(avatar_split_clause,[],[f346,f122,f63,f83])).

fof(f63,plain,
    ( spl8_1
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f346,plain,
    ( v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | spl8_13 ),
    inference(resolution,[],[f123,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ( ! [X3] :
                ( ( ~ r1_orders_2(X0,sK5(X0,X3),X3)
                  & r1_orders_2(X0,sK5(X0,X3),sK4(X0))
                  & r1_orders_2(X0,sK5(X0,X3),sK3(X0))
                  & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,sK4(X0))
                | ~ r1_orders_2(X0,X3,sK3(X0))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ( ! [X8] :
                        ( r1_orders_2(X0,X8,sK6(X0,X5,X6))
                        | ~ r1_orders_2(X0,X8,X6)
                        | ~ r1_orders_2(X0,X8,X5)
                        | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                    & r1_orders_2(X0,sK6(X0,X5,X6),X6)
                    & r1_orders_2(X0,sK6(X0,X5,X6),X5)
                    & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f23,f27,f26,f25,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_orders_2(X0,X4,X2)
                      & r1_orders_2(X0,X4,X1)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X3,X2)
                  | ~ r1_orders_2(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ? [X4] :
                    ( ~ r1_orders_2(X0,X4,X3)
                    & r1_orders_2(X0,X4,X2)
                    & r1_orders_2(X0,X4,sK3(X0))
                    & m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r1_orders_2(X0,X3,X2)
                | ~ r1_orders_2(X0,X3,sK3(X0))
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ? [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  & r1_orders_2(X0,X4,X2)
                  & r1_orders_2(X0,X4,sK3(X0))
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_orders_2(X0,X3,X2)
              | ~ r1_orders_2(X0,X3,sK3(X0))
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ? [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                & r1_orders_2(X0,X4,sK4(X0))
                & r1_orders_2(X0,X4,sK3(X0))
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_orders_2(X0,X3,sK4(X0))
            | ~ r1_orders_2(X0,X3,sK3(X0))
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,sK4(X0))
          & r1_orders_2(X0,X4,sK3(X0))
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X3),X3)
        & r1_orders_2(X0,sK5(X0,X3),sK4(X0))
        & r1_orders_2(X0,sK5(X0,X3),sK3(X0))
        & m1_subset_1(sK5(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X6,X5,X0] :
      ( ? [X7] :
          ( ! [X8] :
              ( r1_orders_2(X0,X8,X7)
              | ~ r1_orders_2(X0,X8,X6)
              | ~ r1_orders_2(X0,X8,X5)
              | ~ m1_subset_1(X8,u1_struct_0(X0)) )
          & r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( ! [X8] :
            ( r1_orders_2(X0,X8,sK6(X0,X5,X6))
            | ~ r1_orders_2(X0,X8,X6)
            | ~ r1_orders_2(X0,X8,X5)
            | ~ m1_subset_1(X8,u1_struct_0(X0)) )
        & r1_orders_2(X0,sK6(X0,X5,X6),X6)
        & r1_orders_2(X0,sK6(X0,X5,X6),X5)
        & m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X5] :
              ( ! [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( r1_orders_2(X0,X8,X7)
                          | ~ r1_orders_2(X0,X8,X6)
                          | ~ r1_orders_2(X0,X8,X5)
                          | ~ m1_subset_1(X8,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X7,X6)
                      & r1_orders_2(X0,X7,X5)
                      & m1_subset_1(X7,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X6,u1_struct_0(X0)) )
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_orders_2(X0,X4,X2)
                        | ~ r1_orders_2(X0,X4,X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r1_orders_2(X0,X4,X2)
                            & r1_orders_2(X0,X4,X1) )
                         => r1_orders_2(X0,X4,X3) ) )
                    & r1_orders_2(X0,X3,X2)
                    & r1_orders_2(X0,X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattice3)).

fof(f123,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f345,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | ~ spl8_18
    | ~ spl8_46
    | ~ spl8_47
    | ~ spl8_13
    | ~ spl8_48
    | ~ spl8_49
    | ~ spl8_14
    | ~ spl8_44 ),
    inference(avatar_split_clause,[],[f332,f318,f127,f343,f340,f122,f337,f334,f148,f83,f87])).

fof(f127,plain,
    ( spl8_14
  <=> ! [X0] :
        ( r1_orders_2(sK0,sK5(sK0,X0),sK4(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3(sK0))
        | ~ r1_orders_2(sK0,X0,sK4(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f318,plain,
    ( spl8_44
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),X0),sK3(sK0))
        | ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),X0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),X0)
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),sK4(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f332,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0))),sK3(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k11_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0)),sK4(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl8_14
    | ~ spl8_44 ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0))),sK3(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k11_lattice3(sK0,sK4(sK0),sK3(sK0)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),sK3(sK0)),sK4(sK0))
    | ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),sK3(sK0)))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl8_14
    | ~ spl8_44 ),
    inference(resolution,[],[f328,f91])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),X0),sK3(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),X0)
        | ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k11_lattice3(sK0,sK4(sK0),X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),X0),sK4(sK0)) )
    | ~ spl8_14
    | ~ spl8_44 ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),X0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),X0)
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),X0),sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k11_lattice3(sK0,sK4(sK0),X0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),X0),sK3(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),X0),sK4(sK0)) )
    | ~ spl8_14
    | ~ spl8_44 ),
    inference(resolution,[],[f319,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK5(sK0,X0),sK4(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3(sK0))
        | ~ r1_orders_2(sK0,X0,sK4(sK0)) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),sK4(sK0))
        | ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),X0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),X0)
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),X0),sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f318])).

fof(f326,plain,
    ( ~ spl8_6
    | spl8_1
    | spl8_18 ),
    inference(avatar_split_clause,[],[f325,f148,f63,f83])).

fof(f325,plain,
    ( v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | spl8_18 ),
    inference(resolution,[],[f149,f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f149,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl8_18 ),
    inference(avatar_component_clause,[],[f148])).

fof(f320,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | ~ spl8_18
    | spl8_44
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f316,f310,f318,f148,f83,f87])).

fof(f310,plain,
    ( spl8_43
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),sK3(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),sK4(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X1,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X1,X0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),X0),sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),sK4(sK0))
        | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),X0)
        | ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),X0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_43 ),
    inference(duplicate_literal_removal,[],[f313])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK4(sK0),X0),sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),sK4(sK0))
        | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,sK4(sK0),X0)),X0)
        | ~ r2_yellow_0(sK0,k2_tarski(sK4(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_43 ),
    inference(resolution,[],[f311,f90])).

fof(f311,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),sK4(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X1,X0)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X1,X0)),X0) )
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f310])).

fof(f312,plain,
    ( ~ spl8_6
    | spl8_43
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f308,f304,f310,f83])).

fof(f304,plain,
    ( spl8_42
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK4(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK3(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f308,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X1,X0)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X1,X0)),X1)
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),sK4(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),sK3(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_42 ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X1,X0)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X1,X0)),X1)
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),sK4(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X1,X0),sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_42 ),
    inference(resolution,[],[f305,f58])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X0)
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK4(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK3(sK0)) )
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f304])).

fof(f306,plain,
    ( ~ spl8_6
    | spl8_1
    | spl8_42
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f302,f160,f304,f63,f83])).

fof(f160,plain,
    ( spl8_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK3(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK4(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X0)
        | ~ m1_subset_1(sK5(sK0,k11_lattice3(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f302,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK3(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK4(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_20 ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK3(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK4(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_lattice3(sK0)
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK4(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK3(sK0))
        | ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_20 ),
    inference(resolution,[],[f161,f43])).

fof(f43,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK5(X0,X3),u1_struct_0(X0))
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK5(sK0,k11_lattice3(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK3(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK4(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f269,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | ~ spl8_4
    | ~ spl8_3
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_34
    | spl8_2
    | spl8_33 ),
    inference(avatar_split_clause,[],[f264,f238,f66,f241,f249,f244,f70,f74,f83,f87])).

fof(f74,plain,
    ( spl8_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f70,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f244,plain,
    ( spl8_35
  <=> m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f249,plain,
    ( spl8_36
  <=> r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f241,plain,
    ( spl8_34
  <=> r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f66,plain,
    ( spl8_2
  <=> r2_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f238,plain,
    ( spl8_33
  <=> m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f264,plain,
    ( r2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK2)
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_33 ),
    inference(resolution,[],[f239,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),u1_struct_0(X0))
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f239,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK0))
    | spl8_33 ),
    inference(avatar_component_clause,[],[f238])).

fof(f262,plain,
    ( ~ spl8_6
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_3
    | spl8_35 ),
    inference(avatar_split_clause,[],[f261,f244,f70,f74,f63,f83])).

fof(f261,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | spl8_35 ),
    inference(resolution,[],[f245,f37])).

fof(f37,plain,(
    ! [X6,X0,X5] :
      ( m1_subset_1(sK6(X0,X5,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f245,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl8_35 ),
    inference(avatar_component_clause,[],[f244])).

fof(f260,plain,
    ( ~ spl8_4
    | ~ spl8_3
    | ~ spl8_10
    | spl8_36 ),
    inference(avatar_split_clause,[],[f259,f249,f106,f70,f74])).

fof(f106,plain,
    ( spl8_10
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,X3,X2),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f259,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_10
    | spl8_36 ),
    inference(resolution,[],[f250,f107])).

fof(f107,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,sK6(sK0,X3,X2),X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f250,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK1)
    | spl8_36 ),
    inference(avatar_component_clause,[],[f249])).

fof(f258,plain,
    ( ~ spl8_4
    | ~ spl8_3
    | ~ spl8_9
    | spl8_34 ),
    inference(avatar_split_clause,[],[f257,f241,f102,f70,f74])).

fof(f102,plain,
    ( spl8_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,X1,X0),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f257,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_9
    | spl8_34 ),
    inference(resolution,[],[f242,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK6(sK0,X1,X0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f242,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK2)
    | spl8_34 ),
    inference(avatar_component_clause,[],[f241])).

fof(f251,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | ~ spl8_4
    | ~ spl8_3
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_34
    | spl8_2
    | spl8_32 ),
    inference(avatar_split_clause,[],[f247,f235,f66,f241,f249,f244,f70,f74,f83,f87])).

fof(f235,plain,
    ( spl8_32
  <=> r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f247,plain,
    ( r2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK2)
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | spl8_32 ),
    inference(resolution,[],[f236,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X1)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f236,plain,
    ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),sK1)
    | spl8_32 ),
    inference(avatar_component_clause,[],[f235])).

fof(f246,plain,
    ( ~ spl8_3
    | ~ spl8_32
    | ~ spl8_4
    | ~ spl8_33
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_10
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f233,f223,f106,f244,f241,f238,f74,f235,f70])).

fof(f223,plain,
    ( spl8_30
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK1)
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK2)
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f233,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_10
    | ~ spl8_30 ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_10
    | ~ spl8_30 ),
    inference(resolution,[],[f224,f107])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK1)
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK2)
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),X0) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f223])).

fof(f225,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | ~ spl8_4
    | ~ spl8_3
    | spl8_2
    | spl8_30
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f221,f213,f223,f66,f70,f74,f83,f87])).

fof(f213,plain,
    ( spl8_28
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),X0)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK1)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK1)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),u1_struct_0(sK0))
        | r2_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK2)
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_28 ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK1)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),u1_struct_0(sK0))
        | r2_yellow_0(sK0,k2_tarski(sK1,sK2))
        | ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK2)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK1)
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_28 ),
    inference(resolution,[],[f214,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X2,X3),X2)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),sK2)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK1)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),u1_struct_0(sK0)) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( ~ spl8_3
    | spl8_28
    | ~ spl8_9
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f211,f205,f102,f213,f70])).

fof(f205,plain,
    ( spl8_27
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK1)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X0)
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X1)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),X0)
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),sK2)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK1) )
    | ~ spl8_9
    | ~ spl8_27 ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),X0)
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,sK2)),sK2)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,sK2),sK1)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_9
    | ~ spl8_27 ),
    inference(resolution,[],[f206,f103])).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK2)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X0)
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X1)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK1) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( ~ spl8_6
    | ~ spl8_1
    | spl8_27
    | ~ spl8_15
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f203,f176,f134,f205,f63,f83])).

fof(f134,plain,
    ( spl8_15
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f176,plain,
    ( spl8_22
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,X0),X0)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK1)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK2)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X0)
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_15
    | ~ spl8_22 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK1)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK2)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_15
    | ~ spl8_22 ),
    inference(resolution,[],[f179,f37])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK1)
        | ~ r1_orders_2(sK0,sK6(sK0,X0,X1),sK2)
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,sK6(sK0,X0,X1)),X0) )
    | ~ spl8_15
    | ~ spl8_22 ),
    inference(resolution,[],[f177,f135])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,X0),X0)
        | ~ r1_orders_2(sK0,X0,sK2)
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | spl8_22
    | spl8_2
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f172,f169,f66,f176,f74,f70])).

fof(f169,plain,
    ( spl8_21
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X2)
        | r2_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2,X0),X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK2) )
    | spl8_2
    | ~ spl8_21 ),
    inference(resolution,[],[f170,f67])).

fof(f67,plain,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( r2_yellow_0(sK0,k2_tarski(X0,X1))
        | ~ r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X2,X1) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( ~ spl8_6
    | spl8_21
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f167,f87,f169,f83])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,sK7(sK0,X0,X1,X2),X2)
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_yellow_0(sK0,k2_tarski(X0,X1)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f57,f88])).

fof(f88,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,sK7(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f162,plain,
    ( ~ spl8_6
    | spl8_1
    | spl8_20
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f158,f153,f79,f160,f63,f83])).

fof(f153,plain,
    ( spl8_19
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X0,k11_lattice3(sK0,X2,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k2_tarski(X2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X1)
        | ~ m1_subset_1(sK5(sK0,k11_lattice3(sK0,X0,X1)),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,k11_lattice3(sK0,X0,X1)),X0)
        | v2_lattice3(sK0)
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK4(sK0))
        | ~ r1_orders_2(sK0,k11_lattice3(sK0,X0,X1),sK3(sK0))
        | ~ m1_subset_1(k11_lattice3(sK0,X0,X1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(resolution,[],[f157,f46])).

fof(f46,plain,(
    ! [X0,X3] :
      ( ~ r1_orders_2(X0,sK5(X0,X3),X3)
      | v2_lattice3(X0)
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,k11_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,k11_lattice3(sK0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_5
    | ~ spl8_19 ),
    inference(resolution,[],[f154,f80])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_yellow_0(sK0,k2_tarski(X2,X1))
        | r1_orders_2(sK0,X0,k11_lattice3(sK0,X2,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,
    ( ~ spl8_6
    | spl8_19
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f151,f87,f153,f83])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k2_tarski(X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,X0,k11_lattice3(sK0,X2,X1)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f92,f88])).

fof(f92,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2)) ) ),
    inference(subsumption_resolution,[],[f59,f58])).

fof(f59,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k11_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f136,plain,
    ( ~ spl8_6
    | spl8_15
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f132,f63,f134,f83])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f40,f77])).

fof(f77,plain,
    ( v2_lattice3(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f40,plain,(
    ! [X6,X0,X8,X5] :
      ( ~ v2_lattice3(X0)
      | ~ r1_orders_2(X0,X8,X6)
      | ~ r1_orders_2(X0,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X8,sK6(X0,X5,X6))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f129,plain,
    ( spl8_1
    | spl8_14
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f125,f83,f127,f63])).

fof(f125,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK5(sK0,X0),sK4(sK0))
        | ~ r1_orders_2(sK0,X0,sK4(sK0))
        | ~ r1_orders_2(sK0,X0,sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_lattice3(sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f45,f84])).

fof(f84,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f45,plain,(
    ! [X0,X3] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK5(X0,X3),sK4(X0))
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,
    ( ~ spl8_6
    | spl8_10
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f99,f63,f106,f83])).

fof(f99,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,X3,X2),X3)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f77,f38])).

fof(f38,plain,(
    ! [X6,X0,X5] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,sK6(X0,X5,X6),X5)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,
    ( ~ spl8_6
    | spl8_9
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f98,f63,f102,f83])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,X1,X0),X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_1 ),
    inference(resolution,[],[f77,f39])).

fof(f39,plain,(
    ! [X6,X0,X5] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,sK6(X0,X5,X6),X6)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,
    ( spl8_1
    | spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f93,f83,f95,f63])).

fof(f93,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK5(sK0,X0),sK3(sK0))
        | ~ r1_orders_2(sK0,X0,sK4(sK0))
        | ~ r1_orders_2(sK0,X0,sK3(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_lattice3(sK0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f44,f84])).

fof(f44,plain,(
    ! [X0,X3] :
      ( ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK5(X0,X3),sK3(X0))
      | ~ r1_orders_2(X0,X3,sK4(X0))
      | ~ r1_orders_2(X0,X3,sK3(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f31,f87])).

fof(f31,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
        & m1_subset_1(sK2,u1_struct_0(sK0))
        & m1_subset_1(sK1,u1_struct_0(sK0)) )
      | ~ v2_lattice3(sK0) )
    & ( ! [X3] :
          ( ! [X4] :
              ( r2_yellow_0(sK0,k2_tarski(X3,X4))
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | v2_lattice3(sK0) )
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ? [X2] :
                  ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_lattice3(X0) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( r2_yellow_0(X0,k2_tarski(X3,X4))
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | v2_lattice3(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(sK0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            & m1_subset_1(X1,u1_struct_0(sK0)) )
        | ~ v2_lattice3(sK0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_yellow_0(sK0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        | v2_lattice3(sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_yellow_0(sK0,k2_tarski(X1,X2))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r2_yellow_0(sK0,k2_tarski(sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ~ r2_yellow_0(sK0,k2_tarski(sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v2_lattice3(X0) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_yellow_0(X0,k2_tarski(X3,X4))
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | v2_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v2_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v2_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ v2_lattice3(X0) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | v2_lattice3(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v2_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( v2_lattice3(X0)
      <~> ! [X1] :
            ( ! [X2] :
                ( r2_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ( v2_lattice3(X0)
        <=> ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r2_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_0)).

fof(f85,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f32,f83])).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f33,f79,f63])).

fof(f33,plain,(
    ! [X4,X3] :
      ( r2_yellow_0(sK0,k2_tarski(X3,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_lattice3(sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f34,f74,f63])).

fof(f34,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f35,f70,f63])).

fof(f35,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f36,f66,f63])).

fof(f36,plain,
    ( ~ r2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
