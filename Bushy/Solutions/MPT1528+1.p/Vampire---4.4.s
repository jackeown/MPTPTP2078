%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t6_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:47 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 391 expanded)
%              Number of leaves         :   22 ( 132 expanded)
%              Depth                    :   12
%              Number of atoms          :  387 (1544 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f82,f89,f96,f114,f126,f128,f130,f132,f134,f138,f139,f146,f153,f162,f164,f166,f168,f170,f174])).

fof(f174,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f172,f74])).

fof(f74,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f172,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f171,f95])).

fof(f95,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f171,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f161,f99])).

fof(f99,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f81,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t6_yellow_0.p',t7_boole)).

fof(f81,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f161,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f59,f113])).

fof(f113,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_11
  <=> ~ r1_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t6_yellow_0.p',d8_lattice3)).

fof(f170,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f154,f99])).

fof(f154,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f74,f113,f95,f59])).

fof(f168,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f155,f113])).

fof(f155,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f74,f95,f99,f59])).

fof(f166,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f165])).

fof(f165,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f158,f95])).

fof(f158,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f74,f113,f99,f59])).

fof(f164,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f159,f74])).

fof(f159,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f95,f113,f99,f59])).

fof(f162,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_11 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f74,f95,f113,f99,f59])).

fof(f153,plain,
    ( spl6_14
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f121,f87,f80,f151])).

fof(f151,plain,
    ( spl6_14
  <=> r2_lattice3(sK5,k1_xboole_0,sK4(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f87,plain,
    ( spl6_4
  <=> l1_orders_2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f121,plain,
    ( r2_lattice3(sK5,k1_xboole_0,sK4(u1_struct_0(sK5)))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f88,f62,f99,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t6_yellow_0.p',d9_lattice3)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t6_yellow_0.p',existence_m1_subset_1)).

fof(f88,plain,
    ( l1_orders_2(sK5)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f146,plain,
    ( spl6_12
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f120,f80,f73,f144])).

fof(f144,plain,
    ( spl6_12
  <=> r2_lattice3(sK0,k1_xboole_0,sK4(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f120,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK4(u1_struct_0(sK0)))
    | ~ spl6_0
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f74,f62,f99,f55])).

fof(f139,plain,
    ( spl6_8
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f119,f94,f80,f73,f103])).

fof(f103,plain,
    ( spl6_8
  <=> r2_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f119,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f74,f95,f99,f55])).

fof(f138,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f136,f74])).

fof(f136,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f135,f95])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f125,f99])).

fof(f125,plain,
    ( r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f55,f107])).

fof(f107,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_9
  <=> ~ r2_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f134,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f118,f99])).

fof(f118,plain,
    ( r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f74,f107,f95,f55])).

fof(f132,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f119,f107])).

fof(f130,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f122,f95])).

fof(f122,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f74,f107,f99,f55])).

fof(f128,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f123,f74])).

fof(f123,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f95,f107,f99,f55])).

fof(f126,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f74,f95,f107,f99,f55])).

fof(f114,plain,
    ( ~ spl6_9
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f51,f112,f106])).

fof(f51,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
    | ~ r2_lattice3(sK0,k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
      | ~ r2_lattice3(sK0,k1_xboole_0,sK1) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
              | ~ r2_lattice3(X0,k1_xboole_0,X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_lattice3(sK0,k1_xboole_0,X1)
            | ~ r2_lattice3(sK0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,k1_xboole_0,sK1)
          | ~ r2_lattice3(X0,k1_xboole_0,sK1) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r1_lattice3(X0,k1_xboole_0,X1)
              & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t6_yellow_0.p',t6_yellow_0)).

fof(f96,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f68,f87])).

fof(f68,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    l1_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f11,f47])).

fof(f47,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK5) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t6_yellow_0.p',existence_l1_orders_2)).

fof(f82,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f52,f80])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t6_yellow_0.p',fc1_xboole_0)).

fof(f75,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f49,f73])).

fof(f49,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
