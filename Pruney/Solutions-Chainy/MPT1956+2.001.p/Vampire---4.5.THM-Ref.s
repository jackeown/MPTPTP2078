%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 328 expanded)
%              Number of leaves         :   37 ( 141 expanded)
%              Depth                    :   12
%              Number of atoms          :  676 (1604 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f82,f86,f90,f94,f98,f102,f115,f119,f130,f132,f134,f143,f147,f152,f157,f163,f169,f181,f190,f192,f197,f203,f209,f215])).

fof(f215,plain,
    ( spl5_9
    | ~ spl5_7
    | ~ spl5_5
    | ~ spl5_4
    | spl5_27 ),
    inference(avatar_split_clause,[],[f214,f207,f84,f88,f96,f109])).

fof(f109,plain,
    ( spl5_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f96,plain,
    ( spl5_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f88,plain,
    ( spl5_5
  <=> v3_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f84,plain,
    ( spl5_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f207,plain,
    ( spl5_27
  <=> r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f214,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_27 ),
    inference(resolution,[],[f208,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
          & r1_yellow_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).

fof(f208,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f207])).

fof(f209,plain,
    ( ~ spl5_4
    | ~ spl5_27
    | spl5_26 ),
    inference(avatar_split_clause,[],[f204,f201,f207,f84])).

fof(f201,plain,
    ( spl5_26
  <=> r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f204,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | spl5_26 ),
    inference(resolution,[],[f202,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f69,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f202,plain,
    ( ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f201])).

fof(f203,plain,
    ( ~ spl5_26
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f199,f195,f80,f201])).

fof(f80,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f195,plain,
    ( spl5_25
  <=> ! [X0] :
        ( ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,sK2))
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f199,plain,
    ( ~ r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(resolution,[],[f196,f81])).

fof(f81,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,sK2)) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( ~ spl5_4
    | ~ spl5_21
    | spl5_25
    | spl5_22 ),
    inference(avatar_split_clause,[],[f193,f179,f195,f176,f84])).

fof(f176,plain,
    ( spl5_21
  <=> m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f179,plain,
    ( spl5_22
  <=> r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,X0,k2_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
        | ~ r1_tarski(sK1,X0)
        | ~ l1_orders_2(sK0) )
    | spl5_22 ),
    inference(resolution,[],[f180,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X1,X3)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f180,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f179])).

fof(f192,plain,
    ( spl5_9
    | ~ spl5_7
    | ~ spl5_5
    | ~ spl5_4
    | spl5_20 ),
    inference(avatar_split_clause,[],[f191,f173,f84,f88,f96,f109])).

fof(f173,plain,
    ( spl5_20
  <=> r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f191,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_20 ),
    inference(resolution,[],[f174,f63])).

fof(f174,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f173])).

fof(f190,plain,
    ( ~ spl5_4
    | spl5_21 ),
    inference(avatar_split_clause,[],[f189,f176,f84])).

fof(f189,plain,
    ( ~ l1_orders_2(sK0)
    | spl5_21 ),
    inference(resolution,[],[f177,f65])).

fof(f177,plain,
    ( ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f176])).

fof(f181,plain,
    ( ~ spl5_4
    | ~ spl5_20
    | ~ spl5_21
    | ~ spl5_22
    | spl5_2 ),
    inference(avatar_split_clause,[],[f170,f76,f179,f176,f173,f84])).

fof(f76,plain,
    ( spl5_2
  <=> r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f170,plain,
    ( ~ r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | spl5_2 ),
    inference(resolution,[],[f77,f106])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f68,f65])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,X4,k2_yellow_0(X0,X1))
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r1_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_yellow_0(X0,X1) != X2
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f169,plain,
    ( spl5_9
    | ~ spl5_7
    | ~ spl5_5
    | ~ spl5_4
    | spl5_18 ),
    inference(avatar_split_clause,[],[f168,f161,f84,f88,f96,f109])).

fof(f161,plain,
    ( spl5_18
  <=> r1_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f168,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_18 ),
    inference(resolution,[],[f162,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f162,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( ~ spl5_4
    | ~ spl5_18
    | spl5_17 ),
    inference(avatar_split_clause,[],[f158,f155,f161,f84])).

fof(f155,plain,
    ( spl5_17
  <=> r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f158,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | spl5_17 ),
    inference(resolution,[],[f156,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f71,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f156,plain,
    ( ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( ~ spl5_17
    | ~ spl5_3
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f153,f150,f80,f155])).

fof(f150,plain,
    ( spl5_16
  <=> ! [X0] :
        ( ~ r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2))
        | ~ r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f153,plain,
    ( ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl5_3
    | ~ spl5_16 ),
    inference(resolution,[],[f151,f81])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2)) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( ~ spl5_4
    | ~ spl5_11
    | spl5_16
    | spl5_15 ),
    inference(avatar_split_clause,[],[f148,f141,f150,f122,f84])).

fof(f122,plain,
    ( spl5_11
  <=> m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f141,plain,
    ( spl5_15
  <=> r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
        | ~ r1_tarski(sK1,X0)
        | ~ l1_orders_2(sK0) )
    | spl5_15 ),
    inference(resolution,[],[f142,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f142,plain,
    ( ~ r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f147,plain,
    ( spl5_9
    | ~ spl5_7
    | ~ spl5_5
    | ~ spl5_4
    | spl5_14 ),
    inference(avatar_split_clause,[],[f144,f138,f84,f88,f96,f109])).

fof(f138,plain,
    ( spl5_14
  <=> r1_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f144,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_14 ),
    inference(resolution,[],[f139,f62])).

fof(f139,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f143,plain,
    ( ~ spl5_4
    | ~ spl5_14
    | ~ spl5_11
    | ~ spl5_15
    | spl5_13 ),
    inference(avatar_split_clause,[],[f135,f128,f141,f122,f138,f84])).

fof(f128,plain,
    ( spl5_13
  <=> r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f135,plain,
    ( ~ r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | spl5_13 ),
    inference(resolution,[],[f129,f104])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f70,f64])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f129,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f134,plain,
    ( ~ spl5_4
    | spl5_12 ),
    inference(avatar_split_clause,[],[f133,f125,f84])).

fof(f125,plain,
    ( spl5_12
  <=> m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f133,plain,
    ( ~ l1_orders_2(sK0)
    | spl5_12 ),
    inference(resolution,[],[f126,f64])).

fof(f126,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f132,plain,
    ( ~ spl5_4
    | spl5_11 ),
    inference(avatar_split_clause,[],[f131,f122,f84])).

fof(f131,plain,
    ( ~ l1_orders_2(sK0)
    | spl5_11 ),
    inference(resolution,[],[f123,f64])).

fof(f123,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f130,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | ~ spl5_13
    | spl5_1
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f120,f113,f73,f128,f125,f122])).

fof(f73,plain,
    ( spl5_1
  <=> r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f113,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f120,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_10 ),
    inference(resolution,[],[f114,f74])).

fof(f74,plain,
    ( ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f119,plain,
    ( ~ spl5_4
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f116,f109,f92,f84])).

fof(f92,plain,
    ( spl5_6
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f116,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f110,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f110,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f115,plain,
    ( spl5_9
    | ~ spl5_8
    | spl5_10
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f107,f84,f113,f100,f109])).

fof(f100,plain,
    ( spl5_8
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f67,f85])).

fof(f85,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f102,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
      | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) )
    & r1_tarski(sK1,sK2)
    & l1_orders_2(sK0)
    & v3_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0)
        & v3_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1))
            | ~ r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK0)
      & v3_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2,X1] :
        ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1))
          | ~ r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2)) )
        & r1_tarski(X1,X2) )
   => ( ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
        | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) )
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ~ r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            | ~ r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0)
      & v3_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_lattice3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
              & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_lattice3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
            & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).

fof(f98,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f44,f92])).

fof(f44,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    v3_lattice3(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f46,f84])).

fof(f46,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f47,f80])).

fof(f47,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f48,f76,f73])).

fof(f48,plain,
    ( ~ r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))
    | ~ r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:48:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (29405)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (29406)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (29415)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (29407)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (29406)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f78,f82,f86,f90,f94,f98,f102,f115,f119,f130,f132,f134,f143,f147,f152,f157,f163,f169,f181,f190,f192,f197,f203,f209,f215])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    spl5_9 | ~spl5_7 | ~spl5_5 | ~spl5_4 | spl5_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f214,f207,f84,f88,f96,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl5_9 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl5_7 <=> v5_orders_2(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl5_5 <=> v3_lattice3(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl5_4 <=> l1_orders_2(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    spl5_27 <=> r2_yellow_0(sK0,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ~l1_orders_2(sK0) | ~v3_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl5_27),
% 0.21/0.51    inference(resolution,[],[f208,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)) | (~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (r2_yellow_0(X0,X1) & r1_yellow_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_0)).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    ~r2_yellow_0(sK0,sK2) | spl5_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f207])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ~spl5_4 | ~spl5_27 | spl5_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f204,f201,f207,f84])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    spl5_26 <=> r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ~r2_yellow_0(sK0,sK2) | ~l1_orders_2(sK0) | spl5_26),
% 0.21/0.51    inference(resolution,[],[f202,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r1_lattice3(X0,X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(rectify,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | k2_yellow_0(X0,X1) != X2)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    ~r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) | spl5_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f201])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    ~spl5_26 | ~spl5_3 | ~spl5_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f199,f195,f80,f201])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl5_3 <=> r1_tarski(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    spl5_25 <=> ! [X0] : (~r1_lattice3(sK0,X0,k2_yellow_0(sK0,sK2)) | ~r1_tarski(sK1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ~r1_lattice3(sK0,sK2,k2_yellow_0(sK0,sK2)) | (~spl5_3 | ~spl5_25)),
% 0.21/0.51    inference(resolution,[],[f196,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r1_lattice3(sK0,X0,k2_yellow_0(sK0,sK2))) ) | ~spl5_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f195])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~spl5_4 | ~spl5_21 | spl5_25 | spl5_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f193,f179,f195,f176,f84])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    spl5_21 <=> m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl5_22 <=> r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_lattice3(sK0,X0,k2_yellow_0(sK0,sK2)) | ~m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) | ~r1_tarski(sK1,X0) | ~l1_orders_2(sK0)) ) | spl5_22),
% 0.21/0.51    inference(resolution,[],[f180,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2)) | spl5_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f179])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    spl5_9 | ~spl5_7 | ~spl5_5 | ~spl5_4 | spl5_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f191,f173,f84,f88,f96,f109])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    spl5_20 <=> r2_yellow_0(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    ~l1_orders_2(sK0) | ~v3_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl5_20),
% 0.21/0.51    inference(resolution,[],[f174,f63])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ~r2_yellow_0(sK0,sK1) | spl5_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f173])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~spl5_4 | spl5_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f189,f176,f84])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ~l1_orders_2(sK0) | spl5_21),
% 0.21/0.51    inference(resolution,[],[f177,f65])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) | spl5_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f176])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ~spl5_4 | ~spl5_20 | ~spl5_21 | ~spl5_22 | spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f170,f76,f179,f176,f173,f84])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl5_2 <=> r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ~r1_lattice3(sK0,sK1,k2_yellow_0(sK0,sK2)) | ~m1_subset_1(k2_yellow_0(sK0,sK2),u1_struct_0(sK0)) | ~r2_yellow_0(sK0,sK1) | ~l1_orders_2(sK0) | spl5_2),
% 0.21/0.51    inference(resolution,[],[f77,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f65])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r1_orders_2(X0,X4,k2_yellow_0(X0,X1)) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r1_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k2_yellow_0(X0,X1) != X2 | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl5_9 | ~spl5_7 | ~spl5_5 | ~spl5_4 | spl5_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f168,f161,f84,f88,f96,f109])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl5_18 <=> r1_yellow_0(sK0,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ~l1_orders_2(sK0) | ~v3_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl5_18),
% 0.21/0.51    inference(resolution,[],[f162,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | ~v3_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ~r1_yellow_0(sK0,sK2) | spl5_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f161])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~spl5_4 | ~spl5_18 | spl5_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f158,f155,f161,f84])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl5_17 <=> r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ~r1_yellow_0(sK0,sK2) | ~l1_orders_2(sK0) | spl5_17),
% 0.21/0.51    inference(resolution,[],[f156,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(rectify,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2)) | spl5_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f155])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ~spl5_17 | ~spl5_3 | ~spl5_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f153,f150,f80,f155])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl5_16 <=> ! [X0] : (~r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2)) | ~r1_tarski(sK1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2)) | (~spl5_3 | ~spl5_16)),
% 0.21/0.51    inference(resolution,[],[f151,f81])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK1,X0) | ~r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2))) ) | ~spl5_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f150])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~spl5_4 | ~spl5_11 | spl5_16 | spl5_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f148,f141,f150,f122,f84])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl5_11 <=> m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl5_15 <=> r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_lattice3(sK0,X0,k1_yellow_0(sK0,sK2)) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | ~r1_tarski(sK1,X0) | ~l1_orders_2(sK0)) ) | spl5_15),
% 0.21/0.51    inference(resolution,[],[f142,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_tarski(X1,X2) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2)) | spl5_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f141])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl5_9 | ~spl5_7 | ~spl5_5 | ~spl5_4 | spl5_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f144,f138,f84,f88,f96,f109])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl5_14 <=> r1_yellow_0(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~l1_orders_2(sK0) | ~v3_lattice3(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | spl5_14),
% 0.21/0.51    inference(resolution,[],[f139,f62])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ~r1_yellow_0(sK0,sK1) | spl5_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ~spl5_4 | ~spl5_14 | ~spl5_11 | ~spl5_15 | spl5_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f135,f128,f141,f122,f138,f84])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl5_13 <=> r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ~r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK2)) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,sK1) | ~l1_orders_2(sK0) | spl5_13),
% 0.21/0.51    inference(resolution,[],[f129,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f64])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) | spl5_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f128])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ~spl5_4 | spl5_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f133,f125,f84])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl5_12 <=> m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ~l1_orders_2(sK0) | spl5_12),
% 0.21/0.51    inference(resolution,[],[f126,f64])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | spl5_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f125])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ~spl5_4 | spl5_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f131,f122,f84])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~l1_orders_2(sK0) | spl5_11),
% 0.21/0.51    inference(resolution,[],[f123,f64])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | spl5_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f122])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ~spl5_11 | ~spl5_12 | ~spl5_13 | spl5_1 | ~spl5_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f120,f113,f73,f128,f125,f122])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl5_1 <=> r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl5_10 <=> ! [X1,X0] : (~r1_orders_2(sK0,X0,X1) | r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) | ~m1_subset_1(k1_yellow_0(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) | (spl5_1 | ~spl5_10)),
% 0.21/0.51    inference(resolution,[],[f114,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) | spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f73])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r3_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ~spl5_4 | ~spl5_6 | ~spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f116,f109,f92,f84])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl5_6 <=> v1_lattice3(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    ~v1_lattice3(sK0) | ~l1_orders_2(sK0) | ~spl5_9),
% 0.21/0.51    inference(resolution,[],[f110,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~spl5_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl5_9 | ~spl5_8 | spl5_10 | ~spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f107,f84,f113,f100,f109])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl5_8 <=> v3_orders_2(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_4),
% 0.21/0.51    inference(resolution,[],[f67,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    l1_orders_2(sK0) | ~spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl5_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f100])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v3_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ((~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))) & r1_tarski(sK1,sK2)) & l1_orders_2(sK0) & v3_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f29,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X2,X1] : ((~r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(sK0) & v3_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ? [X2,X1] : ((~r1_orders_2(sK0,k2_yellow_0(sK0,X2),k2_yellow_0(sK0,X1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,X1),k1_yellow_0(sK0,X2))) & r1_tarski(X1,X2)) => ((~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))) & r1_tarski(sK1,sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1,X2] : ((~r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) | ~r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))) & r1_tarski(X1,X2)) & (l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v3_lattice3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) & r3_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_waybel_7)).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl5_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f96])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    v5_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl5_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f92])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    v1_lattice3(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl5_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f88])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    v3_lattice3(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f84])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    l1_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f80])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~spl5_1 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f76,f73])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~r1_orders_2(sK0,k2_yellow_0(sK0,sK2),k2_yellow_0(sK0,sK1)) | ~r3_orders_2(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (29406)------------------------------
% 0.21/0.51  % (29406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29406)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (29406)Memory used [KB]: 10746
% 0.21/0.51  % (29406)Time elapsed: 0.066 s
% 0.21/0.51  % (29406)------------------------------
% 0.21/0.51  % (29406)------------------------------
% 0.21/0.51  % (29399)Success in time 0.141 s
%------------------------------------------------------------------------------
