%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 201 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   24
%              Number of atoms          :  531 ( 839 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f84,f89,f94,f104,f133,f136,f190,f209])).

fof(f209,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f207,f88])).

fof(f88,plain,
    ( m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f207,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f206,f83])).

fof(f83,plain,
    ( m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f206,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_2
    | spl4_7
    | ~ spl4_9 ),
    inference(resolution,[],[f197,f103])).

fof(f103,plain,
    ( ~ r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_7
  <=> r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f196,f36])).

fof(f36,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f174,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X1,X0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X1,X0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f166,f132])).

fof(f132,plain,
    ( ! [X2,X3] :
        ( ~ r1_orders_2(k2_yellow_1(sK0),X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X3,X2) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_9
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f165,f36])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f125,f51])).

fof(f125,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f124,f34])).

fof(f34,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f124,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f123,f36])).

fof(f123,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f114,f64])).

fof(f64,plain,
    ( v1_lattice3(k2_yellow_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_2
  <=> v1_lattice3(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f114,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0)))
        | ~ v1_lattice3(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6)) )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0)))
        | ~ v1_lattice3(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6))
        | ~ m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(superposition,[],[f53,f73])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( k10_lattice3(k2_yellow_1(sK0),X0,X1) = k13_lattice3(k2_yellow_1(sK0),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f72,f36])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | k10_lattice3(k2_yellow_1(sK0),X0,X1) = k13_lattice3(k2_yellow_1(sK0),X0,X1) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f68,f34])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | k10_lattice3(k2_yellow_1(sK0),X0,X1) = k13_lattice3(k2_yellow_1(sK0),X0,X1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f190,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f188,f88])).

fof(f188,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f187,f83])).

fof(f187,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_9 ),
    inference(resolution,[],[f182,f99])).

fof(f99,plain,
    ( ~ r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_6
  <=> r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f181,f36])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f171,f51])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0)) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f163,f132])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f162,f36])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f122,f51])).

fof(f122,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0)))
        | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f121,f34])).

fof(f121,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f120,f36])).

fof(f120,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f115,f64])).

fof(f115,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0)))
        | ~ v1_lattice3(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4)) )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0)))
        | ~ v1_lattice3(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v5_orders_2(k2_yellow_1(sK0))
        | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4))
        | ~ m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) )
    | ~ spl4_2 ),
    inference(superposition,[],[f54,f73])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f136,plain,
    ( spl4_1
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f134,f59])).

fof(f59,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f134,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f129,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f129,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_8
  <=> v2_struct_0(k2_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f133,plain,
    ( spl4_8
    | spl4_9
    | spl4_1 ),
    inference(avatar_split_clause,[],[f110,f57,f131,f127])).

fof(f110,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,X2)
        | v2_struct_0(k2_yellow_1(sK0)) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f109,f36])).

fof(f109,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,X2)
        | v2_struct_0(k2_yellow_1(sK0)) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f107,f32])).

fof(f32,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f107,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,X2)
        | v2_struct_0(k2_yellow_1(sK0)) )
    | spl4_1 ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ v3_orders_2(k2_yellow_1(sK0))
        | ~ l1_orders_2(k2_yellow_1(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))
        | ~ r1_orders_2(k2_yellow_1(sK0),X3,X2)
        | v2_struct_0(k2_yellow_1(sK0)) )
    | spl4_1 ),
    inference(resolution,[],[f67,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f67,plain,
    ( ! [X2,X3] :
        ( ~ r3_orders_2(k2_yellow_1(sK0),X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))
        | r1_tarski(X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
    | spl4_1 ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f104,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | spl4_5 ),
    inference(avatar_split_clause,[],[f95,f91,f101,f97])).

fof(f91,plain,
    ( spl4_5
  <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f95,plain,
    ( ~ r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_5 ),
    inference(resolution,[],[f93,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f93,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f27,f91])).

fof(f27,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).

fof(f89,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f28,f86])).

fof(f28,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f81])).

fof(f26,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v1_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:10:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (29427)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (29422)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (29419)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (29418)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (29430)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (29426)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (29426)Refutation not found, incomplete strategy% (29426)------------------------------
% 0.21/0.48  % (29426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (29426)Memory used [KB]: 6012
% 0.21/0.48  % (29426)Time elapsed: 0.070 s
% 0.21/0.48  % (29426)------------------------------
% 0.21/0.48  % (29426)------------------------------
% 0.21/0.49  % (29419)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f60,f65,f84,f89,f94,f104,f133,f136,f190,f209])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_7 | ~spl4_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_7 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f207,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl4_4 <=> m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | (~spl4_2 | ~spl4_3 | spl4_7 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f206,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl4_3 <=> m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | (~spl4_2 | spl4_7 | ~spl4_9)),
% 0.21/0.49    inference(resolution,[],[f197,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ~r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl4_7 <=> r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f196,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~l1_orders_2(k2_yellow_1(sK0))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(resolution,[],[f174,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X1,X0))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f173])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X1,X0))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(resolution,[],[f166,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r1_orders_2(k2_yellow_1(sK0),X3,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X3,X2)) ) | ~spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl4_9 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),X3,X2) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X3,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f165,f36])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~l1_orders_2(k2_yellow_1(sK0))) ) | ~spl4_2),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f164])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X1,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))) ) | ~spl4_2),
% 0.21/0.49    inference(resolution,[],[f125,f51])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X6,X5] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6))) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X6,X5] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6))) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f36])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X6,X5] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6))) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f114,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    v1_lattice3(k2_yellow_1(sK0)) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl4_2 <=> v1_lattice3(k2_yellow_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X6,X5] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0))) | ~v1_lattice3(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6))) ) | ~spl4_2),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X6,X5] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X5,X6),u1_struct_0(k2_yellow_1(sK0))) | ~v1_lattice3(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X6,k10_lattice3(k2_yellow_1(sK0),X5,X6)) | ~m1_subset_1(X6,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X5,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.49    inference(superposition,[],[f53,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k10_lattice3(k2_yellow_1(sK0),X0,X1) = k13_lattice3(k2_yellow_1(sK0),X0,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f72,f36])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | k10_lattice3(k2_yellow_1(sK0),X0,X1) = k13_lattice3(k2_yellow_1(sK0),X0,X1)) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f68,f34])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v5_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | k10_lattice3(k2_yellow_1(sK0),X0,X1) = k13_lattice3(k2_yellow_1(sK0),X0,X1)) ) | ~spl4_2),
% 0.21/0.49    inference(resolution,[],[f64,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_lattice3(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))) )),
% 0.21/0.49    inference(equality_resolution,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X2,X3) | k13_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_6 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f188,f88])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | (~spl4_2 | ~spl4_3 | spl4_6 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f187,f83])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | (~spl4_2 | spl4_6 | ~spl4_9)),
% 0.21/0.49    inference(resolution,[],[f182,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl4_6 <=> r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f181,f36])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~l1_orders_2(k2_yellow_1(sK0))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f180])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(resolution,[],[f171,f51])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X1,X0),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X1,k10_lattice3(k2_yellow_1(sK0),X1,X0))) ) | (~spl4_2 | ~spl4_9)),
% 0.21/0.49    inference(resolution,[],[f163,f132])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f162,f36])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~l1_orders_2(k2_yellow_1(sK0))) ) | ~spl4_2),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f161])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X0,k10_lattice3(k2_yellow_1(sK0),X0,X1)) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))) ) | ~spl4_2),
% 0.21/0.49    inference(resolution,[],[f122,f51])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4))) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f121,f34])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4))) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f36])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4))) ) | ~spl4_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f115,f64])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0))) | ~v1_lattice3(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4))) ) | ~spl4_2),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X4,X3] : (~m1_subset_1(k10_lattice3(k2_yellow_1(sK0),X3,X4),u1_struct_0(k2_yellow_1(sK0))) | ~v1_lattice3(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X3,k10_lattice3(k2_yellow_1(sK0),X3,X4)) | ~m1_subset_1(X4,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0)))) ) | ~spl4_2),
% 0.21/0.49    inference(superposition,[],[f54,f73])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))) )),
% 0.21/0.49    inference(equality_resolution,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X1,X3) | k13_lattice3(X0,X1,X2) != X3) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl4_1 | ~spl4_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    $false | (spl4_1 | ~spl4_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f134,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl4_1 <=> v1_xboole_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    v1_xboole_0(sK0) | ~spl4_8),
% 0.21/0.49    inference(resolution,[],[f129,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    v2_struct_0(k2_yellow_1(sK0)) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl4_8 <=> v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl4_8 | spl4_9 | spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f110,f57,f131,f127])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X3,X2) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),X3,X2) | v2_struct_0(k2_yellow_1(sK0))) ) | spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f36])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X3,X2) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~r1_orders_2(k2_yellow_1(sK0),X3,X2) | v2_struct_0(k2_yellow_1(sK0))) ) | spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f107,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X3,X2) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~r1_orders_2(k2_yellow_1(sK0),X3,X2) | v2_struct_0(k2_yellow_1(sK0))) ) | spl4_1),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f106])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X3,X2) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) | ~r1_orders_2(k2_yellow_1(sK0),X3,X2) | v2_struct_0(k2_yellow_1(sK0))) ) | spl4_1),
% 0.21/0.49    inference(resolution,[],[f67,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r3_orders_2(k2_yellow_1(sK0),X2,X3) | ~m1_subset_1(X3,u1_struct_0(k2_yellow_1(sK0))) | r1_tarski(X2,X3) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) ) | spl4_1),
% 0.21/0.49    inference(resolution,[],[f59,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ~spl4_6 | ~spl4_7 | spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f95,f91,f101,f97])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl4_5 <=> r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_5),
% 0.21/0.49    inference(resolution,[],[f93,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f91])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f91])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f86])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f81])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f62])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v1_lattice3(k2_yellow_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f57])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (29419)------------------------------
% 0.21/0.49  % (29419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29419)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (29419)Memory used [KB]: 10746
% 0.21/0.49  % (29419)Time elapsed: 0.088 s
% 0.21/0.49  % (29419)------------------------------
% 0.21/0.49  % (29419)------------------------------
% 0.21/0.49  % (29415)Success in time 0.125 s
%------------------------------------------------------------------------------
