%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 248 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :  783 (1577 expanded)
%              Number of equality atoms :   73 ( 176 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f100,f104,f111,f120,f125,f139,f151,f153,f190,f199,f303,f318])).

fof(f318,plain,
    ( spl5_11
    | ~ spl5_3
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f309,f301,f82,f118])).

fof(f118,plain,
    ( spl5_11
  <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f82,plain,
    ( spl5_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f301,plain,
    ( spl5_36
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,sK2),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f309,plain,
    ( sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ spl5_3
    | ~ spl5_36 ),
    inference(resolution,[],[f302,f83])).

fof(f83,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,sK2),sK2) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f301])).

fof(f303,plain,
    ( spl5_12
    | ~ spl5_7
    | ~ spl5_5
    | ~ spl5_4
    | spl5_36
    | ~ spl5_2
    | ~ spl5_2
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f299,f197,f78,f78,f301,f86,f90,f98,f134])).

fof(f134,plain,
    ( spl5_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f98,plain,
    ( spl5_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f90,plain,
    ( spl5_5
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( spl5_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f78,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f197,plain,
    ( spl5_21
  <=> ! [X3,X2,X4] :
        ( k10_lattice3(sK0,k12_lattice3(sK0,X2,X3),X4) = X4
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k12_lattice3(sK0,X2,X3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,sK2),sK2)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_21 ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,sK2),sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_21 ),
    inference(resolution,[],[f279,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f64,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(superposition,[],[f71,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
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
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,X0,X1),sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,X1),sK2) )
    | ~ spl5_2
    | ~ spl5_21 ),
    inference(resolution,[],[f198,f79])).

fof(f79,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f198,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k12_lattice3(sK0,X2,X3),X4)
        | k10_lattice3(sK0,k12_lattice3(sK0,X2,X3),X4) = X4 )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,
    ( ~ spl5_7
    | ~ spl5_5
    | ~ spl5_4
    | spl5_21
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f193,f188,f197,f86,f90,f98])).

fof(f188,plain,
    ( spl5_20
  <=> ! [X3,X4] :
        ( k10_lattice3(sK0,X3,X4) = X4
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f193,plain,
    ( ! [X4,X2,X3] :
        ( k10_lattice3(sK0,k12_lattice3(sK0,X2,X3),X4) = X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k12_lattice3(sK0,X2,X3),X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl5_20 ),
    inference(resolution,[],[f189,f64])).

fof(f189,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k10_lattice3(sK0,X3,X4) = X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X4) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f188])).

fof(f190,plain,
    ( spl5_12
    | ~ spl5_8
    | ~ spl5_4
    | spl5_20
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f185,f149,f188,f86,f102,f134])).

fof(f102,plain,
    ( spl5_8
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f149,plain,
    ( spl5_15
  <=> ! [X3,X2] :
        ( k10_lattice3(sK0,X2,X3) = X3
        | ~ r1_orders_2(sK0,X3,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f185,plain,
    ( ! [X4,X3] :
        ( k10_lattice3(sK0,X3,X4) = X4
        | ~ r1_orders_2(sK0,X3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_15 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ! [X4,X3] :
        ( k10_lattice3(sK0,X3,X4) = X4
        | ~ r1_orders_2(sK0,X3,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_15 ),
    inference(resolution,[],[f150,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(f150,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(sK0,X3,X3)
        | k10_lattice3(sK0,X2,X3) = X3
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f153,plain,
    ( ~ spl5_4
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f152,f134,f94,f86])).

fof(f94,plain,
    ( spl5_6
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f152,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f135,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f135,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f151,plain,
    ( spl5_12
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_4
    | spl5_15
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f142,f137,f149,f86,f94,f98,f134])).

fof(f137,plain,
    ( spl5_13
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f142,plain,
    ( ! [X2,X3] :
        ( k10_lattice3(sK0,X2,X3) = X3
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X3,X3)
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_13 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( ! [X2,X3] :
        ( k10_lattice3(sK0,X2,X3) = X3
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ r1_orders_2(sK0,X3,X3)
        | k10_lattice3(sK0,X2,X3) = X3
        | ~ r1_orders_2(sK0,X3,X3)
        | ~ r1_orders_2(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f138,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
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
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0))
        | k10_lattice3(sK0,X1,X2) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X2,X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( spl5_12
    | ~ spl5_6
    | ~ spl5_4
    | spl5_13
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f132,f98,f137,f86,f94,f134])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | k10_lattice3(sK0,X1,X2) = X0
        | v2_struct_0(sK0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f56,f99])).

fof(f99,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | k10_lattice3(X0,X1,X2) = X3
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f125,plain,
    ( ~ spl5_7
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_3
    | ~ spl5_2
    | spl5_10 ),
    inference(avatar_split_clause,[],[f121,f114,f78,f82,f86,f90,f98])).

fof(f114,plain,
    ( spl5_10
  <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f121,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_10 ),
    inference(resolution,[],[f115,f64])).

fof(f115,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f120,plain,
    ( ~ spl5_10
    | ~ spl5_2
    | ~ spl5_11
    | spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f112,f109,f74,f118,f78,f114])).

fof(f74,plain,
    ( spl5_1
  <=> sK2 = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f109,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f112,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_9 ),
    inference(superposition,[],[f75,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f75,plain,
    ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f111,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f105,f98,f109,f86,f94])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f65,f99])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f104,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f40,f102])).

fof(f40,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).

fof(f100,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f41,f98])).

fof(f41,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f42,f94])).

fof(f42,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f88,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f45,f82])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f46,f78])).

fof(f46,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f47,f74])).

fof(f47,plain,(
    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:15:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (16646)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.43  % (16646)Refutation not found, incomplete strategy% (16646)------------------------------
% 0.20/0.43  % (16646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (16646)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (16646)Memory used [KB]: 6140
% 0.20/0.43  % (16646)Time elapsed: 0.004 s
% 0.20/0.43  % (16646)------------------------------
% 0.20/0.43  % (16646)------------------------------
% 0.20/0.46  % (16640)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (16648)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (16654)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (16639)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (16635)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (16640)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f331,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f76,f80,f84,f88,f92,f96,f100,f104,f111,f120,f125,f139,f151,f153,f190,f199,f303,f318])).
% 0.20/0.48  fof(f318,plain,(
% 0.20/0.48    spl5_11 | ~spl5_3 | ~spl5_36),
% 0.20/0.48    inference(avatar_split_clause,[],[f309,f301,f82,f118])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl5_11 <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl5_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.48  fof(f301,plain,(
% 0.20/0.48    spl5_36 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,sK2),sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.20/0.48  fof(f309,plain,(
% 0.20/0.48    sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | (~spl5_3 | ~spl5_36)),
% 0.20/0.48    inference(resolution,[],[f302,f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f82])).
% 0.20/0.48  fof(f302,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,sK2),sK2)) ) | ~spl5_36),
% 0.20/0.48    inference(avatar_component_clause,[],[f301])).
% 0.20/0.48  fof(f303,plain,(
% 0.20/0.48    spl5_12 | ~spl5_7 | ~spl5_5 | ~spl5_4 | spl5_36 | ~spl5_2 | ~spl5_2 | ~spl5_21),
% 0.20/0.48    inference(avatar_split_clause,[],[f299,f197,f78,f78,f301,f86,f90,f98,f134])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    spl5_12 <=> v2_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl5_7 <=> v5_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl5_5 <=> v2_lattice3(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl5_4 <=> l1_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl5_2 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    spl5_21 <=> ! [X3,X2,X4] : (k10_lattice3(sK0,k12_lattice3(sK0,X2,X3),X4) = X4 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k12_lattice3(sK0,X2,X3),X4) | ~m1_subset_1(X4,u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.48  fof(f299,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,sK2),sK2) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_21)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f296])).
% 0.20/0.48  fof(f296,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_21)),
% 0.20/0.48    inference(resolution,[],[f279,f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(global_subsumption,[],[f64,f127])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f126])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.48    inference(superposition,[],[f71,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(rectify,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).
% 0.20/0.48  fof(f279,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_orders_2(sK0,k12_lattice3(sK0,X0,X1),sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK2 = k10_lattice3(sK0,k12_lattice3(sK0,X0,X1),sK2)) ) | (~spl5_2 | ~spl5_21)),
% 0.20/0.48    inference(resolution,[],[f198,f79])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f78])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    ( ! [X4,X2,X3] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k12_lattice3(sK0,X2,X3),X4) | k10_lattice3(sK0,k12_lattice3(sK0,X2,X3),X4) = X4) ) | ~spl5_21),
% 0.20/0.48    inference(avatar_component_clause,[],[f197])).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    ~spl5_7 | ~spl5_5 | ~spl5_4 | spl5_21 | ~spl5_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f193,f188,f197,f86,f90,f98])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    spl5_20 <=> ! [X3,X4] : (k10_lattice3(sK0,X3,X4) = X4 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X4))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    ( ! [X4,X2,X3] : (k10_lattice3(sK0,k12_lattice3(sK0,X2,X3),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k12_lattice3(sK0,X2,X3),X4) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)) ) | ~spl5_20),
% 0.20/0.48    inference(resolution,[],[f189,f64])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k10_lattice3(sK0,X3,X4) = X4 | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X4)) ) | ~spl5_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f188])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    spl5_12 | ~spl5_8 | ~spl5_4 | spl5_20 | ~spl5_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f185,f149,f188,f86,f102,f134])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl5_8 <=> v3_orders_2(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    spl5_15 <=> ! [X3,X2] : (k10_lattice3(sK0,X2,X3) = X3 | ~r1_orders_2(sK0,X3,X3) | ~r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    ( ! [X4,X3] : (k10_lattice3(sK0,X3,X4) = X4 | ~r1_orders_2(sK0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_15),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f184])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    ( ! [X4,X3] : (k10_lattice3(sK0,X3,X4) = X4 | ~r1_orders_2(sK0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_15),
% 0.20/0.48    inference(resolution,[],[f150,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~r1_orders_2(sK0,X3,X3) | k10_lattice3(sK0,X2,X3) = X3 | ~r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl5_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f149])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ~spl5_4 | ~spl5_6 | ~spl5_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f152,f134,f94,f86])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl5_6 <=> v1_lattice3(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl5_12),
% 0.20/0.48    inference(resolution,[],[f135,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~spl5_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f134])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    spl5_12 | ~spl5_7 | ~spl5_6 | ~spl5_4 | spl5_15 | ~spl5_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f142,f137,f149,f86,f94,f98,f134])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    spl5_13 <=> ! [X1,X0,X2] : (~r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0)) | k10_lattice3(sK0,X1,X2) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~r1_orders_2(sK0,X2,X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k10_lattice3(sK0,X2,X3) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | ~r1_orders_2(sK0,X3,X3) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_13),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f141])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k10_lattice3(sK0,X2,X3) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X3) | ~r1_orders_2(sK0,X3,X3) | k10_lattice3(sK0,X2,X3) = X3 | ~r1_orders_2(sK0,X3,X3) | ~r1_orders_2(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_13),
% 0.20/0.48    inference(resolution,[],[f138,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(rectify,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0)) | k10_lattice3(sK0,X1,X2) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~r1_orders_2(sK0,X2,X0)) ) | ~spl5_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f137])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    spl5_12 | ~spl5_6 | ~spl5_4 | spl5_13 | ~spl5_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f132,f98,f137,f86,f94,f134])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,sK3(sK0,X1,X2,X0)) | ~r1_orders_2(sK0,X2,X0) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | k10_lattice3(sK0,X1,X2) = X0 | v2_struct_0(sK0)) ) | ~spl5_7),
% 0.20/0.49    inference(resolution,[],[f56,f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    v5_orders_2(sK0) | ~spl5_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f98])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | k10_lattice3(X0,X1,X2) = X3 | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ~spl5_7 | ~spl5_5 | ~spl5_4 | ~spl5_3 | ~spl5_2 | spl5_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f121,f114,f78,f82,f86,f90,f98])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl5_10 <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_10),
% 0.20/0.49    inference(resolution,[],[f115,f64])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl5_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ~spl5_10 | ~spl5_2 | ~spl5_11 | spl5_1 | ~spl5_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f112,f109,f74,f118,f78,f114])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    spl5_1 <=> sK2 = k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl5_9 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl5_1 | ~spl5_9)),
% 0.20/0.49    inference(superposition,[],[f75,f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f109])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ~spl5_6 | ~spl5_4 | spl5_9 | ~spl5_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f105,f98,f109,f86,f94])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | k10_lattice3(sK0,X1,X0) = k13_lattice3(sK0,X1,X0)) ) | ~spl5_7),
% 0.20/0.49    inference(resolution,[],[f65,f99])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    spl5_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f102])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    v3_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ((sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f28,f27,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) => (sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 0.20/0.49    inference(negated_conjecture,[],[f8])).
% 0.20/0.49  fof(f8,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattice3)).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    spl5_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f98])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    v5_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl5_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f94])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    v1_lattice3(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl5_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f90])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    v2_lattice3(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f86])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    l1_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f82])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f46,f78])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f47,f74])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (16640)------------------------------
% 0.20/0.49  % (16640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16640)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (16640)Memory used [KB]: 10874
% 0.20/0.49  % (16640)Time elapsed: 0.026 s
% 0.20/0.49  % (16640)------------------------------
% 0.20/0.49  % (16640)------------------------------
% 0.20/0.49  % (16634)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (16647)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (16644)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (16643)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (16629)Success in time 0.133 s
%------------------------------------------------------------------------------
