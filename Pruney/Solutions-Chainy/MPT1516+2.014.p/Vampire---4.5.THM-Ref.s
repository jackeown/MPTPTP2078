%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:50 EST 2020

% Result     : Theorem 33.84s
% Output     : Refutation 33.84s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 713 expanded)
%              Number of leaves         :   37 ( 264 expanded)
%              Depth                    :   15
%              Number of atoms          : 1017 (2873 expanded)
%              Number of equality atoms :  142 ( 254 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53990,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f201,f202,f207,f208,f209,f337,f342,f347,f352,f357,f362,f424,f519,f884,f5839,f53989])).

fof(f53989,plain,
    ( spl12_1
    | ~ spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10
    | ~ spl12_11
    | ~ spl12_12 ),
    inference(avatar_contradiction_clause,[],[f53988])).

fof(f53988,plain,
    ( $false
    | spl12_1
    | ~ spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10
    | ~ spl12_11
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f53972,f7870])).

fof(f7870,plain,
    ( ! [X42] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X42)))
    | spl12_1
    | ~ spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_12 ),
    inference(superposition,[],[f1248,f1166])).

fof(f1166,plain,
    ( ! [X0] : sK2(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X0))))
    | spl12_1
    | ~ spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f183,f187,f206,f195,f532,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(f532,plain,
    ( ! [X0] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
    | spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f183,f361,f192,f293,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
                  & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f77,f79,f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
              & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f293,plain,
    ( ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
    | spl12_1
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f183,f195,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f192,plain,
    ( ~ v13_lattices(sK0)
    | spl12_3 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl12_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f361,plain,
    ( l1_lattices(sK0)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl12_12
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f195,plain,
    ( l3_lattices(sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl12_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f206,plain,
    ( v4_lattice3(sK0)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl12_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f187,plain,
    ( v10_lattices(sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl12_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f183,plain,
    ( ~ v2_struct_0(sK0)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl12_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f1248,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9 ),
    inference(unit_resulting_resolution,[],[f183,f341,f336,f195,f293,f293,f621,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f621,plain,
    ( ! [X0] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9 ),
    inference(unit_resulting_resolution,[],[f183,f346,f341,f336,f195,f293,f293,f365,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f365,plain,
    ( ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(unit_resulting_resolution,[],[f112,f183,f187,f195,f206,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

fof(f112,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f346,plain,
    ( v6_lattices(sK0)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl12_9
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f336,plain,
    ( v9_lattices(sK0)
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl12_7
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f341,plain,
    ( v8_lattices(sK0)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl12_8
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f53972,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl12_1
    | ~ spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10
    | ~ spl12_11
    | ~ spl12_12 ),
    inference(trivial_inequality_removal,[],[f53959])).

fof(f53959,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl12_1
    | ~ spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10
    | ~ spl12_11
    | ~ spl12_12 ),
    inference(superposition,[],[f592,f18919])).

fof(f18919,plain,
    ( ! [X4] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X4)),k15_lattice3(sK0,k1_xboole_0))
    | spl12_1
    | ~ spl12_2
    | spl12_3
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10
    | ~ spl12_11
    | ~ spl12_12 ),
    inference(superposition,[],[f18861,f1166])).

fof(f18861,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_10
    | ~ spl12_11
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f183,f351,f356,f293,f540,f2018,f12281,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(f12281,plain,
    ( ! [X37,X36] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k2_lattices(sK0,k15_lattice3(sK0,X36),k15_lattice3(sK0,X37)))
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_12 ),
    inference(superposition,[],[f621,f1427])).

fof(f1427,plain,
    ( ! [X0,X1] : k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))))
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f183,f187,f206,f195,f540,f137])).

fof(f2018,plain,
    ( ! [X0,X1] : r1_lattices(sK0,k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)),k15_lattice3(sK0,X1))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_11
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f183,f356,f293,f540,f536,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f536,plain,
    ( ! [X0,X1] : k15_lattice3(sK0,X0) = k1_lattices(sK0,k2_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X0)),k15_lattice3(sK0,X0))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_8 ),
    inference(unit_resulting_resolution,[],[f183,f195,f341,f293,f293,f149])).

fof(f149,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f89,f91,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0))
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(f540,plain,
    ( ! [X0,X1] : m1_subset_1(k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)),u1_struct_0(sK0))
    | spl12_1
    | ~ spl12_4
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f183,f361,f293,f293,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f356,plain,
    ( l2_lattices(sK0)
    | ~ spl12_11 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl12_11
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f351,plain,
    ( v4_lattices(sK0)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl12_10
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f592,plain,
    ( ! [X28] :
        ( k15_lattice3(sK0,X28) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X28)),k15_lattice3(sK0,X28))
        | k15_lattice3(sK0,X28) != k2_lattices(sK0,k15_lattice3(sK0,X28),sK2(sK0,k15_lattice3(sK0,X28))) )
    | spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f591,f183])).

fof(f591,plain,
    ( ! [X28] :
        ( k15_lattice3(sK0,X28) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X28)),k15_lattice3(sK0,X28))
        | k15_lattice3(sK0,X28) != k2_lattices(sK0,k15_lattice3(sK0,X28),sK2(sK0,k15_lattice3(sK0,X28)))
        | v2_struct_0(sK0) )
    | spl12_1
    | spl12_3
    | ~ spl12_4
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f590,f361])).

fof(f590,plain,
    ( ! [X28] :
        ( k15_lattice3(sK0,X28) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X28)),k15_lattice3(sK0,X28))
        | k15_lattice3(sK0,X28) != k2_lattices(sK0,k15_lattice3(sK0,X28),sK2(sK0,k15_lattice3(sK0,X28)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl12_1
    | spl12_3
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f560,f192])).

fof(f560,plain,
    ( ! [X28] :
        ( v13_lattices(sK0)
        | k15_lattice3(sK0,X28) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X28)),k15_lattice3(sK0,X28))
        | k15_lattice3(sK0,X28) != k2_lattices(sK0,k15_lattice3(sK0,X28),sK2(sK0,k15_lattice3(sK0,X28)))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl12_1
    | ~ spl12_4 ),
    inference(resolution,[],[f293,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f5839,plain,
    ( spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | spl12_5
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_17
    | ~ spl12_36 ),
    inference(avatar_contradiction_clause,[],[f5838])).

fof(f5838,plain,
    ( $false
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | spl12_5
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_17
    | ~ spl12_36 ),
    inference(subsumption_resolution,[],[f5837,f200])).

fof(f200,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl12_5 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl12_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f5837,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_17
    | ~ spl12_36 ),
    inference(forward_demodulation,[],[f5826,f883])).

fof(f883,plain,
    ( ! [X60] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0))
    | ~ spl12_36 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl12_36
  <=> ! [X60] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f5826,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_7
    | ~ spl12_8
    | ~ spl12_9
    | ~ spl12_17 ),
    inference(superposition,[],[f1248,f496])).

fof(f496,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl12_17 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl12_17
  <=> k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f884,plain,
    ( ~ spl12_3
    | spl12_36
    | spl12_1
    | ~ spl12_4
    | ~ spl12_12
    | ~ spl12_13 ),
    inference(avatar_split_clause,[],[f880,f421,f359,f194,f182,f882,f190])).

fof(f421,plain,
    ( spl12_13
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f880,plain,
    ( ! [X60] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0))
        | ~ v13_lattices(sK0) )
    | spl12_1
    | ~ spl12_4
    | ~ spl12_12
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f879,f183])).

fof(f879,plain,
    ( ! [X60] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl12_1
    | ~ spl12_4
    | ~ spl12_12
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f878,f361])).

fof(f878,plain,
    ( ! [X60] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl12_1
    | ~ spl12_4
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f577,f423])).

fof(f423,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f421])).

fof(f577,plain,
    ( ! [X60] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl12_1
    | ~ spl12_4 ),
    inference(resolution,[],[f293,f171])).

fof(f171,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f73,f74])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f519,plain,
    ( spl12_17
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_13 ),
    inference(avatar_split_clause,[],[f518,f421,f204,f194,f186,f182,f494])).

fof(f518,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f517,f183])).

fof(f517,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f516,f187])).

fof(f516,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f515,f206])).

fof(f515,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f450,f195])).

fof(f450,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_13 ),
    inference(resolution,[],[f423,f137])).

fof(f424,plain,
    ( spl12_13
    | spl12_1
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f408,f359,f182,f421])).

fof(f408,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl12_1
    | ~ spl12_12 ),
    inference(unit_resulting_resolution,[],[f183,f361,f125])).

fof(f125,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f362,plain,
    ( spl12_12
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f287,f194,f359])).

fof(f287,plain,
    ( l1_lattices(sK0)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f195,f113])).

fof(f113,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f357,plain,
    ( spl12_11
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f288,f194,f354])).

fof(f288,plain,
    ( l2_lattices(sK0)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f195,f114])).

fof(f114,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f352,plain,
    ( spl12_10
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f289,f194,f186,f182,f349])).

fof(f289,plain,
    ( v4_lattices(sK0)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f183,f187,f195,f116])).

fof(f116,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f347,plain,
    ( spl12_9
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f290,f194,f186,f182,f344])).

fof(f290,plain,
    ( v6_lattices(sK0)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f183,f187,f195,f117])).

fof(f117,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f342,plain,
    ( spl12_8
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f291,f194,f186,f182,f339])).

fof(f291,plain,
    ( v8_lattices(sK0)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f183,f187,f195,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f337,plain,
    ( spl12_7
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f292,f194,f186,f182,f334])).

fof(f292,plain,
    ( v9_lattices(sK0)
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f183,f187,f195,f119])).

fof(f119,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f209,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f107,f182])).

fof(f107,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f68])).

fof(f68,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
        | ~ l3_lattices(sK0)
        | ~ v13_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f208,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f108,f186])).

fof(f108,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f207,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f109,f204])).

fof(f109,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f202,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f110,f194])).

fof(f110,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f69])).

fof(f201,plain,
    ( spl12_1
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4
    | ~ spl12_5 ),
    inference(avatar_split_clause,[],[f111,f198,f194,f190,f186,f182])).

fof(f111,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:51:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (9232)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (9230)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (9224)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (9218)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (9218)Refutation not found, incomplete strategy% (9218)------------------------------
% 0.21/0.53  % (9218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9218)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (9218)Memory used [KB]: 1663
% 0.21/0.53  % (9218)Time elapsed: 0.002 s
% 0.21/0.53  % (9218)------------------------------
% 0.21/0.53  % (9218)------------------------------
% 0.21/0.54  % (9219)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (9233)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (9220)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (9221)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (9243)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (9242)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (9244)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (9229)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (9225)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (9236)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (9235)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (9237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (9223)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (9235)Refutation not found, incomplete strategy% (9235)------------------------------
% 0.21/0.55  % (9235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9235)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9235)Memory used [KB]: 10618
% 0.21/0.55  % (9235)Time elapsed: 0.132 s
% 0.21/0.55  % (9235)------------------------------
% 0.21/0.55  % (9235)------------------------------
% 0.21/0.55  % (9222)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (9245)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (9234)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (9246)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (9240)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (9227)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (9229)Refutation not found, incomplete strategy% (9229)------------------------------
% 0.21/0.56  % (9229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9226)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (9238)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (9247)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (9228)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (9228)Refutation not found, incomplete strategy% (9228)------------------------------
% 0.21/0.57  % (9228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9228)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9228)Memory used [KB]: 10746
% 0.21/0.57  % (9228)Time elapsed: 0.168 s
% 0.21/0.57  % (9228)------------------------------
% 0.21/0.57  % (9228)------------------------------
% 0.21/0.57  % (9239)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (9241)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (9227)Refutation not found, incomplete strategy% (9227)------------------------------
% 0.21/0.57  % (9227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (9231)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.57/0.58  % (9229)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (9229)Memory used [KB]: 10746
% 1.57/0.58  % (9229)Time elapsed: 0.158 s
% 1.57/0.58  % (9229)------------------------------
% 1.57/0.58  % (9229)------------------------------
% 1.57/0.58  % (9227)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (9227)Memory used [KB]: 10618
% 1.57/0.58  % (9227)Time elapsed: 0.005 s
% 1.57/0.58  % (9227)------------------------------
% 1.57/0.58  % (9227)------------------------------
% 1.57/0.58  % (9240)Refutation not found, incomplete strategy% (9240)------------------------------
% 1.57/0.58  % (9240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (9240)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.58  
% 1.57/0.58  % (9240)Memory used [KB]: 10874
% 1.57/0.58  % (9240)Time elapsed: 0.140 s
% 1.57/0.58  % (9240)------------------------------
% 1.57/0.58  % (9240)------------------------------
% 2.14/0.66  % (9248)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.53/0.72  % (9250)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.53/0.73  % (9251)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.53/0.75  % (9249)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.53/0.75  % (9253)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.88/0.77  % (9252)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.88/0.82  % (9223)Time limit reached!
% 2.88/0.82  % (9223)------------------------------
% 2.88/0.82  % (9223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.88/0.82  % (9223)Termination reason: Time limit
% 2.88/0.82  % (9223)Termination phase: Saturation
% 2.88/0.82  
% 2.88/0.82  % (9223)Memory used [KB]: 8315
% 2.88/0.82  % (9223)Time elapsed: 0.400 s
% 2.88/0.82  % (9223)------------------------------
% 2.88/0.82  % (9223)------------------------------
% 3.81/0.91  % (9219)Time limit reached!
% 3.81/0.91  % (9219)------------------------------
% 3.81/0.91  % (9219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.93  % (9219)Termination reason: Time limit
% 3.81/0.93  
% 3.81/0.93  % (9219)Memory used [KB]: 8315
% 3.81/0.93  % (9219)Time elapsed: 0.505 s
% 3.81/0.93  % (9219)------------------------------
% 3.81/0.93  % (9219)------------------------------
% 3.81/0.93  % (9230)Time limit reached!
% 3.81/0.93  % (9230)------------------------------
% 3.81/0.93  % (9230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.93  % (9230)Termination reason: Time limit
% 3.81/0.93  % (9230)Termination phase: Saturation
% 3.81/0.93  
% 3.81/0.93  % (9230)Memory used [KB]: 10746
% 3.81/0.93  % (9230)Time elapsed: 0.500 s
% 3.81/0.93  % (9230)------------------------------
% 3.81/0.93  % (9230)------------------------------
% 4.12/0.98  % (9254)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.12/1.00  % (9252)Time limit reached!
% 4.12/1.00  % (9252)------------------------------
% 4.12/1.00  % (9252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/1.00  % (9252)Termination reason: Time limit
% 4.12/1.00  % (9252)Termination phase: Saturation
% 4.12/1.00  
% 4.12/1.00  % (9252)Memory used [KB]: 12281
% 4.12/1.00  % (9252)Time elapsed: 0.400 s
% 4.12/1.00  % (9252)------------------------------
% 4.12/1.00  % (9252)------------------------------
% 4.56/1.01  % (9246)Time limit reached!
% 4.56/1.01  % (9246)------------------------------
% 4.56/1.01  % (9246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/1.01  % (9246)Termination reason: Time limit
% 4.56/1.01  
% 4.56/1.01  % (9246)Memory used [KB]: 7164
% 4.56/1.01  % (9246)Time elapsed: 0.608 s
% 4.56/1.01  % (9246)------------------------------
% 4.56/1.01  % (9246)------------------------------
% 4.56/1.02  % (9234)Time limit reached!
% 4.56/1.02  % (9234)------------------------------
% 4.56/1.02  % (9234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/1.02  % (9234)Termination reason: Time limit
% 4.56/1.02  
% 4.56/1.02  % (9234)Memory used [KB]: 16758
% 4.56/1.02  % (9234)Time elapsed: 0.616 s
% 4.56/1.02  % (9234)------------------------------
% 4.56/1.02  % (9234)------------------------------
% 4.56/1.04  % (9225)Time limit reached!
% 4.56/1.04  % (9225)------------------------------
% 4.56/1.04  % (9225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/1.04  % (9225)Termination reason: Time limit
% 4.56/1.04  
% 4.56/1.04  % (9225)Memory used [KB]: 9850
% 4.56/1.04  % (9225)Time elapsed: 0.631 s
% 4.56/1.04  % (9225)------------------------------
% 4.56/1.04  % (9225)------------------------------
% 4.56/1.05  % (9251)Time limit reached!
% 4.56/1.05  % (9251)------------------------------
% 4.56/1.05  % (9251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.56/1.05  % (9251)Termination reason: Time limit
% 4.56/1.05  
% 4.56/1.05  % (9251)Memory used [KB]: 7036
% 4.56/1.05  % (9251)Time elapsed: 0.431 s
% 4.56/1.05  % (9251)------------------------------
% 4.56/1.05  % (9251)------------------------------
% 5.50/1.10  % (9256)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.50/1.11  % (9255)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.50/1.15  % (9258)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.50/1.15  % (9259)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.50/1.16  % (9257)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.28/1.18  % (9260)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.28/1.20  % (9239)Time limit reached!
% 6.28/1.20  % (9239)------------------------------
% 6.28/1.20  % (9239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.28/1.20  % (9239)Termination reason: Time limit
% 6.28/1.20  % (9239)Termination phase: Saturation
% 6.28/1.20  
% 6.28/1.20  % (9239)Memory used [KB]: 4349
% 6.28/1.20  % (9239)Time elapsed: 0.800 s
% 6.28/1.20  % (9239)------------------------------
% 6.28/1.20  % (9239)------------------------------
% 6.62/1.22  % (9261)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.86/1.29  % (9262)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 8.07/1.43  % (9220)Time limit reached!
% 8.07/1.43  % (9220)------------------------------
% 8.07/1.43  % (9220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.07/1.44  % (9220)Termination reason: Time limit
% 8.07/1.44  
% 8.07/1.44  % (9220)Memory used [KB]: 17910
% 8.07/1.44  % (9220)Time elapsed: 1.023 s
% 8.07/1.44  % (9220)------------------------------
% 8.07/1.44  % (9220)------------------------------
% 9.15/1.58  % (9263)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 9.15/1.61  % (9260)Time limit reached!
% 9.15/1.61  % (9260)------------------------------
% 9.15/1.61  % (9260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.15/1.61  % (9260)Termination reason: Time limit
% 9.15/1.61  
% 9.15/1.61  % (9260)Memory used [KB]: 2686
% 9.15/1.61  % (9260)Time elapsed: 0.526 s
% 9.15/1.61  % (9260)------------------------------
% 9.15/1.61  % (9260)------------------------------
% 9.81/1.64  % (9244)Time limit reached!
% 9.81/1.64  % (9244)------------------------------
% 9.81/1.64  % (9244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.81/1.64  % (9244)Termination reason: Time limit
% 9.81/1.64  
% 9.81/1.64  % (9244)Memory used [KB]: 19573
% 9.81/1.64  % (9244)Time elapsed: 1.219 s
% 9.81/1.64  % (9244)------------------------------
% 9.81/1.64  % (9244)------------------------------
% 10.55/1.72  % (9242)Time limit reached!
% 10.55/1.72  % (9242)------------------------------
% 10.55/1.72  % (9242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.55/1.72  % (9242)Termination reason: Time limit
% 10.55/1.72  % (9242)Termination phase: Saturation
% 10.55/1.72  
% 10.55/1.72  % (9242)Memory used [KB]: 18933
% 10.55/1.72  % (9242)Time elapsed: 1.300 s
% 10.55/1.72  % (9242)------------------------------
% 10.55/1.72  % (9242)------------------------------
% 10.55/1.72  % (9233)Time limit reached!
% 10.55/1.72  % (9233)------------------------------
% 10.55/1.72  % (9233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.55/1.73  % (9264)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 10.55/1.74  % (9233)Termination reason: Time limit
% 10.55/1.74  % (9233)Termination phase: Saturation
% 10.55/1.74  
% 10.55/1.74  % (9233)Memory used [KB]: 16630
% 10.55/1.74  % (9233)Time elapsed: 1.300 s
% 10.55/1.74  % (9233)------------------------------
% 10.55/1.74  % (9233)------------------------------
% 11.13/1.80  % (9265)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.52/1.85  % (9267)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 11.52/1.92  % (9245)Time limit reached!
% 11.52/1.92  % (9245)------------------------------
% 11.52/1.92  % (9245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.52/1.92  % (9245)Termination reason: Time limit
% 11.52/1.92  
% 11.52/1.92  % (9245)Memory used [KB]: 10874
% 11.52/1.92  % (9245)Time elapsed: 1.506 s
% 11.52/1.92  % (9245)------------------------------
% 11.52/1.92  % (9245)------------------------------
% 12.24/1.96  % (9268)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 12.77/2.05  % (9264)Time limit reached!
% 12.77/2.05  % (9264)------------------------------
% 12.77/2.05  % (9264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.77/2.05  % (9264)Termination reason: Time limit
% 12.77/2.05  
% 12.77/2.05  % (9264)Memory used [KB]: 4093
% 12.77/2.05  % (9264)Time elapsed: 0.415 s
% 12.77/2.05  % (9264)------------------------------
% 12.77/2.05  % (9264)------------------------------
% 12.77/2.05  % (9254)Time limit reached!
% 12.77/2.05  % (9254)------------------------------
% 12.77/2.05  % (9254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.77/2.06  % (9254)Termination reason: Time limit
% 12.77/2.06  
% 12.77/2.06  % (9254)Memory used [KB]: 13432
% 12.77/2.06  % (9254)Time elapsed: 1.210 s
% 12.77/2.06  % (9254)------------------------------
% 12.77/2.06  % (9254)------------------------------
% 13.54/2.12  % (9222)Time limit reached!
% 13.54/2.12  % (9222)------------------------------
% 13.54/2.12  % (9222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.54/2.12  % (9222)Termination reason: Time limit
% 13.54/2.12  
% 13.54/2.12  % (9222)Memory used [KB]: 18549
% 13.54/2.12  % (9222)Time elapsed: 1.686 s
% 13.54/2.12  % (9222)------------------------------
% 13.54/2.12  % (9222)------------------------------
% 13.71/2.14  % (9269)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.71/2.17  % (9271)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 13.71/2.20  % (9270)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 13.71/2.22  % (9268)Time limit reached!
% 13.71/2.22  % (9268)------------------------------
% 13.71/2.22  % (9268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.71/2.22  % (9268)Termination reason: Time limit
% 13.71/2.22  
% 13.71/2.22  % (9268)Memory used [KB]: 2046
% 13.71/2.22  % (9268)Time elapsed: 0.420 s
% 13.71/2.22  % (9268)------------------------------
% 13.71/2.22  % (9268)------------------------------
% 14.77/2.25  % (9272)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 15.35/2.31  % (9250)Time limit reached!
% 15.35/2.31  % (9250)------------------------------
% 15.35/2.31  % (9250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.35/2.31  % (9250)Termination reason: Time limit
% 15.35/2.31  
% 15.35/2.31  % (9250)Memory used [KB]: 14456
% 15.35/2.31  % (9250)Time elapsed: 1.721 s
% 15.35/2.31  % (9250)------------------------------
% 15.35/2.31  % (9250)------------------------------
% 15.35/2.32  % (9232)Time limit reached!
% 15.35/2.32  % (9232)------------------------------
% 15.35/2.32  % (9232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.35/2.32  % (9232)Termination reason: Time limit
% 15.35/2.32  
% 15.35/2.32  % (9232)Memory used [KB]: 8699
% 15.35/2.32  % (9232)Time elapsed: 1.836 s
% 15.35/2.32  % (9232)------------------------------
% 15.35/2.32  % (9232)------------------------------
% 15.96/2.41  % (9273)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 15.96/2.43  % (9272)Refutation not found, incomplete strategy% (9272)------------------------------
% 15.96/2.43  % (9272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.96/2.43  % (9272)Termination reason: Refutation not found, incomplete strategy
% 15.96/2.43  
% 15.96/2.43  % (9272)Memory used [KB]: 6140
% 15.96/2.43  % (9272)Time elapsed: 0.275 s
% 15.96/2.43  % (9272)------------------------------
% 15.96/2.43  % (9272)------------------------------
% 15.96/2.43  % (9236)Time limit reached!
% 15.96/2.43  % (9236)------------------------------
% 15.96/2.43  % (9236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.96/2.43  % (9236)Termination reason: Time limit
% 15.96/2.43  
% 15.96/2.43  % (9236)Memory used [KB]: 14839
% 15.96/2.43  % (9236)Time elapsed: 2.029 s
% 15.96/2.43  % (9236)------------------------------
% 15.96/2.43  % (9236)------------------------------
% 15.96/2.46  % (9274)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 15.96/2.46  % (9275)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 15.96/2.47  % (9275)Refutation not found, incomplete strategy% (9275)------------------------------
% 15.96/2.47  % (9275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.96/2.47  % (9275)Termination reason: Refutation not found, incomplete strategy
% 15.96/2.47  
% 15.96/2.47  % (9275)Memory used [KB]: 6268
% 15.96/2.47  % (9275)Time elapsed: 0.104 s
% 15.96/2.47  % (9275)------------------------------
% 15.96/2.47  % (9275)------------------------------
% 17.04/2.53  % (9224)Time limit reached!
% 17.04/2.53  % (9224)------------------------------
% 17.04/2.53  % (9224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.04/2.53  % (9224)Termination reason: Time limit
% 17.04/2.53  
% 17.04/2.53  % (9224)Memory used [KB]: 21108
% 17.04/2.53  % (9224)Time elapsed: 2.019 s
% 17.04/2.53  % (9224)------------------------------
% 17.04/2.53  % (9224)------------------------------
% 17.04/2.57  % (9276)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 17.67/2.64  % (9273)Time limit reached!
% 17.67/2.64  % (9273)------------------------------
% 17.67/2.64  % (9273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.67/2.64  % (9273)Termination reason: Time limit
% 17.67/2.64  % (9273)Termination phase: Saturation
% 17.67/2.64  
% 17.67/2.64  % (9273)Memory used [KB]: 9850
% 17.67/2.64  % (9273)Time elapsed: 0.400 s
% 17.67/2.64  % (9273)------------------------------
% 17.67/2.64  % (9273)------------------------------
% 18.23/2.72  % (9256)Time limit reached!
% 18.23/2.72  % (9256)------------------------------
% 18.23/2.72  % (9256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.23/2.72  % (9256)Termination reason: Time limit
% 18.23/2.72  
% 18.23/2.72  % (9256)Memory used [KB]: 15735
% 18.23/2.72  % (9256)Time elapsed: 1.723 s
% 18.23/2.72  % (9256)------------------------------
% 18.23/2.72  % (9256)------------------------------
% 18.23/2.75  % (9263)Time limit reached!
% 18.23/2.75  % (9263)------------------------------
% 18.23/2.75  % (9263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.23/2.75  % (9263)Termination reason: Time limit
% 18.23/2.75  % (9263)Termination phase: Saturation
% 18.23/2.75  
% 18.23/2.75  % (9263)Memory used [KB]: 19957
% 18.23/2.75  % (9263)Time elapsed: 1.200 s
% 18.23/2.75  % (9263)------------------------------
% 18.23/2.75  % (9263)------------------------------
% 20.26/2.97  % (9226)Time limit reached!
% 20.26/2.97  % (9226)------------------------------
% 20.26/2.97  % (9226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.26/2.97  % (9226)Termination reason: Time limit
% 20.26/2.97  
% 20.26/2.97  % (9226)Memory used [KB]: 31726
% 20.26/2.97  % (9226)Time elapsed: 2.543 s
% 20.26/2.97  % (9226)------------------------------
% 20.26/2.97  % (9226)------------------------------
% 20.82/3.02  % (9237)Time limit reached!
% 20.82/3.02  % (9237)------------------------------
% 20.82/3.02  % (9237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.82/3.02  % (9237)Termination reason: Time limit
% 20.82/3.02  
% 20.82/3.02  % (9237)Memory used [KB]: 26609
% 20.82/3.02  % (9237)Time elapsed: 2.618 s
% 20.82/3.02  % (9237)------------------------------
% 20.82/3.02  % (9237)------------------------------
% 22.01/3.13  % (9267)Time limit reached!
% 22.01/3.13  % (9267)------------------------------
% 22.01/3.13  % (9267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 22.01/3.14  % (9267)Termination reason: Time limit
% 22.01/3.14  % (9267)Termination phase: Saturation
% 22.01/3.14  
% 22.01/3.14  % (9267)Memory used [KB]: 12920
% 22.01/3.14  % (9267)Time elapsed: 1.300 s
% 22.01/3.14  % (9267)------------------------------
% 22.01/3.14  % (9267)------------------------------
% 24.10/3.40  % (9231)Time limit reached!
% 24.10/3.40  % (9231)------------------------------
% 24.10/3.40  % (9231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.10/3.40  % (9231)Termination reason: Time limit
% 24.10/3.40  % (9231)Termination phase: Saturation
% 24.10/3.40  
% 24.10/3.40  % (9231)Memory used [KB]: 20340
% 24.10/3.40  % (9231)Time elapsed: 3.0000 s
% 24.10/3.40  % (9231)------------------------------
% 24.10/3.40  % (9231)------------------------------
% 27.47/3.82  % (9249)Time limit reached!
% 27.47/3.82  % (9249)------------------------------
% 27.47/3.82  % (9249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.47/3.82  % (9249)Termination reason: Time limit
% 27.47/3.82  
% 27.47/3.82  % (9249)Memory used [KB]: 6652
% 27.47/3.82  % (9249)Time elapsed: 3.218 s
% 27.47/3.82  % (9249)------------------------------
% 27.47/3.82  % (9249)------------------------------
% 31.34/4.33  % (9247)Time limit reached!
% 31.34/4.33  % (9247)------------------------------
% 31.34/4.33  % (9247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.34/4.33  % (9247)Termination reason: Time limit
% 31.34/4.33  % (9247)Termination phase: Saturation
% 31.34/4.33  
% 31.34/4.33  % (9247)Memory used [KB]: 19829
% 31.34/4.33  % (9247)Time elapsed: 3.900 s
% 31.34/4.33  % (9247)------------------------------
% 31.34/4.33  % (9247)------------------------------
% 33.84/4.63  % (9243)Refutation found. Thanks to Tanya!
% 33.84/4.63  % SZS status Theorem for theBenchmark
% 33.84/4.63  % SZS output start Proof for theBenchmark
% 33.84/4.64  fof(f53990,plain,(
% 33.84/4.64    $false),
% 33.84/4.64    inference(avatar_sat_refutation,[],[f201,f202,f207,f208,f209,f337,f342,f347,f352,f357,f362,f424,f519,f884,f5839,f53989])).
% 33.84/4.64  fof(f53989,plain,(
% 33.84/4.64    spl12_1 | ~spl12_2 | spl12_3 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_10 | ~spl12_11 | ~spl12_12),
% 33.84/4.64    inference(avatar_contradiction_clause,[],[f53988])).
% 33.84/4.64  fof(f53988,plain,(
% 33.84/4.64    $false | (spl12_1 | ~spl12_2 | spl12_3 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_10 | ~spl12_11 | ~spl12_12)),
% 33.84/4.64    inference(subsumption_resolution,[],[f53972,f7870])).
% 33.84/4.64  fof(f7870,plain,(
% 33.84/4.64    ( ! [X42] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X42)))) ) | (spl12_1 | ~spl12_2 | spl12_3 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_12)),
% 33.84/4.64    inference(superposition,[],[f1248,f1166])).
% 33.84/4.64  fof(f1166,plain,(
% 33.84/4.64    ( ! [X0] : (sK2(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X0))))) ) | (spl12_1 | ~spl12_2 | spl12_3 | ~spl12_4 | ~spl12_6 | ~spl12_12)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f187,f206,f195,f532,f137])).
% 33.84/4.64  fof(f137,plain,(
% 33.84/4.64    ( ! [X0,X1] : (k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f47])).
% 33.84/4.64  fof(f47,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f46])).
% 33.84/4.64  fof(f46,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f19])).
% 33.84/4.64  fof(f19,axiom,(
% 33.84/4.64    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).
% 33.84/4.64  fof(f532,plain,(
% 33.84/4.64    ( ! [X0] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))) ) | (spl12_1 | spl12_3 | ~spl12_4 | ~spl12_12)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f361,f192,f293,f133])).
% 33.84/4.64  fof(f133,plain,(
% 33.84/4.64    ( ! [X0,X1] : (v13_lattices(X0) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f80])).
% 33.84/4.64  fof(f80,plain,(
% 33.84/4.64    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f77,f79,f78])).
% 33.84/4.64  fof(f78,plain,(
% 33.84/4.64    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 33.84/4.64    introduced(choice_axiom,[])).
% 33.84/4.64  fof(f79,plain,(
% 33.84/4.64    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 33.84/4.64    introduced(choice_axiom,[])).
% 33.84/4.64  fof(f77,plain,(
% 33.84/4.64    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(rectify,[],[f76])).
% 33.84/4.64  fof(f76,plain,(
% 33.84/4.64    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(nnf_transformation,[],[f43])).
% 33.84/4.64  fof(f43,plain,(
% 33.84/4.64    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f42])).
% 33.84/4.64  fof(f42,plain,(
% 33.84/4.64    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f14])).
% 33.84/4.64  fof(f14,axiom,(
% 33.84/4.64    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 33.84/4.64  fof(f293,plain,(
% 33.84/4.64    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl12_1 | ~spl12_4)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f195,f157])).
% 33.84/4.64  fof(f157,plain,(
% 33.84/4.64    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f59])).
% 33.84/4.64  fof(f59,plain,(
% 33.84/4.64    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f58])).
% 33.84/4.64  fof(f58,plain,(
% 33.84/4.64    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f17])).
% 33.84/4.64  fof(f17,axiom,(
% 33.84/4.64    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 33.84/4.64  fof(f192,plain,(
% 33.84/4.64    ~v13_lattices(sK0) | spl12_3),
% 33.84/4.64    inference(avatar_component_clause,[],[f190])).
% 33.84/4.64  fof(f190,plain,(
% 33.84/4.64    spl12_3 <=> v13_lattices(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 33.84/4.64  fof(f361,plain,(
% 33.84/4.64    l1_lattices(sK0) | ~spl12_12),
% 33.84/4.64    inference(avatar_component_clause,[],[f359])).
% 33.84/4.64  fof(f359,plain,(
% 33.84/4.64    spl12_12 <=> l1_lattices(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 33.84/4.64  fof(f195,plain,(
% 33.84/4.64    l3_lattices(sK0) | ~spl12_4),
% 33.84/4.64    inference(avatar_component_clause,[],[f194])).
% 33.84/4.64  fof(f194,plain,(
% 33.84/4.64    spl12_4 <=> l3_lattices(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 33.84/4.64  fof(f206,plain,(
% 33.84/4.64    v4_lattice3(sK0) | ~spl12_6),
% 33.84/4.64    inference(avatar_component_clause,[],[f204])).
% 33.84/4.64  fof(f204,plain,(
% 33.84/4.64    spl12_6 <=> v4_lattice3(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 33.84/4.64  fof(f187,plain,(
% 33.84/4.64    v10_lattices(sK0) | ~spl12_2),
% 33.84/4.64    inference(avatar_component_clause,[],[f186])).
% 33.84/4.64  fof(f186,plain,(
% 33.84/4.64    spl12_2 <=> v10_lattices(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 33.84/4.64  fof(f183,plain,(
% 33.84/4.64    ~v2_struct_0(sK0) | spl12_1),
% 33.84/4.64    inference(avatar_component_clause,[],[f182])).
% 33.84/4.64  fof(f182,plain,(
% 33.84/4.64    spl12_1 <=> v2_struct_0(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 33.84/4.64  fof(f1248,plain,(
% 33.84/4.64    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f341,f336,f195,f293,f293,f621,f123])).
% 33.84/4.64  fof(f123,plain,(
% 33.84/4.64    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f71])).
% 33.84/4.64  fof(f71,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(nnf_transformation,[],[f37])).
% 33.84/4.64  fof(f37,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f36])).
% 33.84/4.64  fof(f36,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f12])).
% 33.84/4.64  fof(f12,axiom,(
% 33.84/4.64    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 33.84/4.64  fof(f621,plain,(
% 33.84/4.64    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f346,f341,f336,f195,f293,f293,f365,f162])).
% 33.84/4.64  fof(f162,plain,(
% 33.84/4.64    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f101])).
% 33.84/4.64  fof(f101,plain,(
% 33.84/4.64    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(nnf_transformation,[],[f63])).
% 33.84/4.64  fof(f63,plain,(
% 33.84/4.64    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f62])).
% 33.84/4.64  fof(f62,plain,(
% 33.84/4.64    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f11])).
% 33.84/4.64  fof(f11,axiom,(
% 33.84/4.64    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 33.84/4.64  fof(f365,plain,(
% 33.84/4.64    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f112,f183,f187,f195,f206,f139])).
% 33.84/4.64  fof(f139,plain,(
% 33.84/4.64    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~r1_tarski(X1,X2) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f49])).
% 33.84/4.64  fof(f49,plain,(
% 33.84/4.64    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f48])).
% 33.84/4.64  fof(f48,plain,(
% 33.84/4.64    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f20])).
% 33.84/4.64  fof(f20,axiom,(
% 33.84/4.64    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).
% 33.84/4.64  fof(f112,plain,(
% 33.84/4.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f2])).
% 33.84/4.64  fof(f2,axiom,(
% 33.84/4.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 33.84/4.64  fof(f346,plain,(
% 33.84/4.64    v6_lattices(sK0) | ~spl12_9),
% 33.84/4.64    inference(avatar_component_clause,[],[f344])).
% 33.84/4.64  fof(f344,plain,(
% 33.84/4.64    spl12_9 <=> v6_lattices(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 33.84/4.64  fof(f336,plain,(
% 33.84/4.64    v9_lattices(sK0) | ~spl12_7),
% 33.84/4.64    inference(avatar_component_clause,[],[f334])).
% 33.84/4.64  fof(f334,plain,(
% 33.84/4.64    spl12_7 <=> v9_lattices(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 33.84/4.64  fof(f341,plain,(
% 33.84/4.64    v8_lattices(sK0) | ~spl12_8),
% 33.84/4.64    inference(avatar_component_clause,[],[f339])).
% 33.84/4.64  fof(f339,plain,(
% 33.84/4.64    spl12_8 <=> v8_lattices(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 33.84/4.64  fof(f53972,plain,(
% 33.84/4.64    k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | (spl12_1 | ~spl12_2 | spl12_3 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_10 | ~spl12_11 | ~spl12_12)),
% 33.84/4.64    inference(trivial_inequality_removal,[],[f53959])).
% 33.84/4.64  fof(f53959,plain,(
% 33.84/4.64    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | k15_lattice3(sK0,k1_xboole_0) != k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,k1_xboole_0))) | (spl12_1 | ~spl12_2 | spl12_3 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_10 | ~spl12_11 | ~spl12_12)),
% 33.84/4.64    inference(superposition,[],[f592,f18919])).
% 33.84/4.64  fof(f18919,plain,(
% 33.84/4.64    ( ! [X4] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X4)),k15_lattice3(sK0,k1_xboole_0))) ) | (spl12_1 | ~spl12_2 | spl12_3 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_10 | ~spl12_11 | ~spl12_12)),
% 33.84/4.64    inference(superposition,[],[f18861,f1166])).
% 33.84/4.64  fof(f18861,plain,(
% 33.84/4.64    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,k1_xboole_0))) ) | (spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_10 | ~spl12_11 | ~spl12_12)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f351,f356,f293,f540,f2018,f12281,f120])).
% 33.84/4.64  fof(f120,plain,(
% 33.84/4.64    ( ! [X2,X0,X1] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f33])).
% 33.84/4.64  fof(f33,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f32])).
% 33.84/4.64  fof(f32,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f13])).
% 33.84/4.64  fof(f13,axiom,(
% 33.84/4.64    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).
% 33.84/4.64  fof(f12281,plain,(
% 33.84/4.64    ( ! [X37,X36] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k2_lattices(sK0,k15_lattice3(sK0,X36),k15_lattice3(sK0,X37)))) ) | (spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_12)),
% 33.84/4.64    inference(superposition,[],[f621,f1427])).
% 33.84/4.64  fof(f1427,plain,(
% 33.84/4.64    ( ! [X0,X1] : (k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))))) ) | (spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_12)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f187,f206,f195,f540,f137])).
% 33.84/4.64  fof(f2018,plain,(
% 33.84/4.64    ( ! [X0,X1] : (r1_lattices(sK0,k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)),k15_lattice3(sK0,X1))) ) | (spl12_1 | ~spl12_4 | ~spl12_8 | ~spl12_11 | ~spl12_12)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f356,f293,f540,f536,f122])).
% 33.84/4.64  fof(f122,plain,(
% 33.84/4.64    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f70])).
% 33.84/4.64  fof(f70,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(nnf_transformation,[],[f35])).
% 33.84/4.64  fof(f35,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f34])).
% 33.84/4.64  fof(f34,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f6])).
% 33.84/4.64  fof(f6,axiom,(
% 33.84/4.64    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 33.84/4.64  fof(f536,plain,(
% 33.84/4.64    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k1_lattices(sK0,k2_lattices(sK0,k15_lattice3(sK0,X1),k15_lattice3(sK0,X0)),k15_lattice3(sK0,X0))) ) | (spl12_1 | ~spl12_4 | ~spl12_8)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f195,f341,f293,f293,f149])).
% 33.84/4.64  fof(f149,plain,(
% 33.84/4.64    ( ! [X4,X0,X3] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f92])).
% 33.84/4.64  fof(f92,plain,(
% 33.84/4.64    ! [X0] : (((v8_lattices(X0) | ((sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0)) & m1_subset_1(sK7(X0),u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f89,f91,f90])).
% 33.84/4.64  fof(f90,plain,(
% 33.84/4.64    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 33.84/4.64    introduced(choice_axiom,[])).
% 33.84/4.64  fof(f91,plain,(
% 33.84/4.64    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0)) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 33.84/4.64    introduced(choice_axiom,[])).
% 33.84/4.64  fof(f89,plain,(
% 33.84/4.64    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(rectify,[],[f88])).
% 33.84/4.64  fof(f88,plain,(
% 33.84/4.64    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(nnf_transformation,[],[f55])).
% 33.84/4.64  fof(f55,plain,(
% 33.84/4.64    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f54])).
% 33.84/4.64  fof(f54,plain,(
% 33.84/4.64    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f7])).
% 33.84/4.64  fof(f7,axiom,(
% 33.84/4.64    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 33.84/4.64  fof(f540,plain,(
% 33.84/4.64    ( ! [X0,X1] : (m1_subset_1(k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)),u1_struct_0(sK0))) ) | (spl12_1 | ~spl12_4 | ~spl12_12)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f361,f293,f293,f164])).
% 33.84/4.64  fof(f164,plain,(
% 33.84/4.64    ( ! [X2,X0,X1] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f65])).
% 33.84/4.64  fof(f65,plain,(
% 33.84/4.64    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f64])).
% 33.84/4.64  fof(f64,plain,(
% 33.84/4.64    ! [X0,X1,X2] : (m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f8])).
% 33.84/4.64  fof(f8,axiom,(
% 33.84/4.64    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).
% 33.84/4.64  fof(f356,plain,(
% 33.84/4.64    l2_lattices(sK0) | ~spl12_11),
% 33.84/4.64    inference(avatar_component_clause,[],[f354])).
% 33.84/4.64  fof(f354,plain,(
% 33.84/4.64    spl12_11 <=> l2_lattices(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 33.84/4.64  fof(f351,plain,(
% 33.84/4.64    v4_lattices(sK0) | ~spl12_10),
% 33.84/4.64    inference(avatar_component_clause,[],[f349])).
% 33.84/4.64  fof(f349,plain,(
% 33.84/4.64    spl12_10 <=> v4_lattices(sK0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 33.84/4.64  fof(f592,plain,(
% 33.84/4.64    ( ! [X28] : (k15_lattice3(sK0,X28) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X28)),k15_lattice3(sK0,X28)) | k15_lattice3(sK0,X28) != k2_lattices(sK0,k15_lattice3(sK0,X28),sK2(sK0,k15_lattice3(sK0,X28)))) ) | (spl12_1 | spl12_3 | ~spl12_4 | ~spl12_12)),
% 33.84/4.64    inference(subsumption_resolution,[],[f591,f183])).
% 33.84/4.64  fof(f591,plain,(
% 33.84/4.64    ( ! [X28] : (k15_lattice3(sK0,X28) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X28)),k15_lattice3(sK0,X28)) | k15_lattice3(sK0,X28) != k2_lattices(sK0,k15_lattice3(sK0,X28),sK2(sK0,k15_lattice3(sK0,X28))) | v2_struct_0(sK0)) ) | (spl12_1 | spl12_3 | ~spl12_4 | ~spl12_12)),
% 33.84/4.64    inference(subsumption_resolution,[],[f590,f361])).
% 33.84/4.64  fof(f590,plain,(
% 33.84/4.64    ( ! [X28] : (k15_lattice3(sK0,X28) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X28)),k15_lattice3(sK0,X28)) | k15_lattice3(sK0,X28) != k2_lattices(sK0,k15_lattice3(sK0,X28),sK2(sK0,k15_lattice3(sK0,X28))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl12_1 | spl12_3 | ~spl12_4)),
% 33.84/4.64    inference(subsumption_resolution,[],[f560,f192])).
% 33.84/4.64  fof(f560,plain,(
% 33.84/4.64    ( ! [X28] : (v13_lattices(sK0) | k15_lattice3(sK0,X28) != k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X28)),k15_lattice3(sK0,X28)) | k15_lattice3(sK0,X28) != k2_lattices(sK0,k15_lattice3(sK0,X28),sK2(sK0,k15_lattice3(sK0,X28))) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl12_1 | ~spl12_4)),
% 33.84/4.64    inference(resolution,[],[f293,f134])).
% 33.84/4.64  fof(f134,plain,(
% 33.84/4.64    ( ! [X0,X1] : (v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f80])).
% 33.84/4.64  fof(f5839,plain,(
% 33.84/4.64    spl12_1 | ~spl12_2 | ~spl12_4 | spl12_5 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_17 | ~spl12_36),
% 33.84/4.64    inference(avatar_contradiction_clause,[],[f5838])).
% 33.84/4.64  fof(f5838,plain,(
% 33.84/4.64    $false | (spl12_1 | ~spl12_2 | ~spl12_4 | spl12_5 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_17 | ~spl12_36)),
% 33.84/4.64    inference(subsumption_resolution,[],[f5837,f200])).
% 33.84/4.64  fof(f200,plain,(
% 33.84/4.64    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl12_5),
% 33.84/4.64    inference(avatar_component_clause,[],[f198])).
% 33.84/4.64  fof(f198,plain,(
% 33.84/4.64    spl12_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 33.84/4.64  fof(f5837,plain,(
% 33.84/4.64    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_17 | ~spl12_36)),
% 33.84/4.64    inference(forward_demodulation,[],[f5826,f883])).
% 33.84/4.64  fof(f883,plain,(
% 33.84/4.64    ( ! [X60] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0))) ) | ~spl12_36),
% 33.84/4.64    inference(avatar_component_clause,[],[f882])).
% 33.84/4.64  fof(f882,plain,(
% 33.84/4.64    spl12_36 <=> ! [X60] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0))),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).
% 33.84/4.64  fof(f5826,plain,(
% 33.84/4.64    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_7 | ~spl12_8 | ~spl12_9 | ~spl12_17)),
% 33.84/4.64    inference(superposition,[],[f1248,f496])).
% 33.84/4.64  fof(f496,plain,(
% 33.84/4.64    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~spl12_17),
% 33.84/4.64    inference(avatar_component_clause,[],[f494])).
% 33.84/4.64  fof(f494,plain,(
% 33.84/4.64    spl12_17 <=> k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).
% 33.84/4.64  fof(f884,plain,(
% 33.84/4.64    ~spl12_3 | spl12_36 | spl12_1 | ~spl12_4 | ~spl12_12 | ~spl12_13),
% 33.84/4.64    inference(avatar_split_clause,[],[f880,f421,f359,f194,f182,f882,f190])).
% 33.84/4.64  fof(f421,plain,(
% 33.84/4.64    spl12_13 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 33.84/4.64    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 33.84/4.64  fof(f880,plain,(
% 33.84/4.64    ( ! [X60] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0)) | ~v13_lattices(sK0)) ) | (spl12_1 | ~spl12_4 | ~spl12_12 | ~spl12_13)),
% 33.84/4.64    inference(subsumption_resolution,[],[f879,f183])).
% 33.84/4.64  fof(f879,plain,(
% 33.84/4.64    ( ! [X60] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0)) | ~v13_lattices(sK0) | v2_struct_0(sK0)) ) | (spl12_1 | ~spl12_4 | ~spl12_12 | ~spl12_13)),
% 33.84/4.64    inference(subsumption_resolution,[],[f878,f361])).
% 33.84/4.64  fof(f878,plain,(
% 33.84/4.64    ( ! [X60] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl12_1 | ~spl12_4 | ~spl12_13)),
% 33.84/4.64    inference(subsumption_resolution,[],[f577,f423])).
% 33.84/4.64  fof(f423,plain,(
% 33.84/4.64    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl12_13),
% 33.84/4.64    inference(avatar_component_clause,[],[f421])).
% 33.84/4.64  fof(f577,plain,(
% 33.84/4.64    ( ! [X60] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X60),k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (spl12_1 | ~spl12_4)),
% 33.84/4.64    inference(resolution,[],[f293,f171])).
% 33.84/4.64  fof(f171,plain,(
% 33.84/4.64    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(equality_resolution,[],[f127])).
% 33.84/4.64  fof(f127,plain,(
% 33.84/4.64    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f75])).
% 33.84/4.64  fof(f75,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f73,f74])).
% 33.84/4.64  fof(f74,plain,(
% 33.84/4.64    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 33.84/4.64    introduced(choice_axiom,[])).
% 33.84/4.64  fof(f73,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(rectify,[],[f72])).
% 33.84/4.64  fof(f72,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(nnf_transformation,[],[f41])).
% 33.84/4.64  fof(f41,plain,(
% 33.84/4.64    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f40])).
% 33.84/4.64  fof(f40,plain,(
% 33.84/4.64    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f5])).
% 33.84/4.64  fof(f5,axiom,(
% 33.84/4.64    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 33.84/4.64  fof(f519,plain,(
% 33.84/4.64    spl12_17 | spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_13),
% 33.84/4.64    inference(avatar_split_clause,[],[f518,f421,f204,f194,f186,f182,f494])).
% 33.84/4.64  fof(f518,plain,(
% 33.84/4.64    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | (spl12_1 | ~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_13)),
% 33.84/4.64    inference(subsumption_resolution,[],[f517,f183])).
% 33.84/4.64  fof(f517,plain,(
% 33.84/4.64    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl12_2 | ~spl12_4 | ~spl12_6 | ~spl12_13)),
% 33.84/4.64    inference(subsumption_resolution,[],[f516,f187])).
% 33.84/4.64  fof(f516,plain,(
% 33.84/4.64    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl12_4 | ~spl12_6 | ~spl12_13)),
% 33.84/4.64    inference(subsumption_resolution,[],[f515,f206])).
% 33.84/4.64  fof(f515,plain,(
% 33.84/4.64    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (~spl12_4 | ~spl12_13)),
% 33.84/4.64    inference(subsumption_resolution,[],[f450,f195])).
% 33.84/4.64  fof(f450,plain,(
% 33.84/4.64    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl12_13),
% 33.84/4.64    inference(resolution,[],[f423,f137])).
% 33.84/4.64  fof(f424,plain,(
% 33.84/4.64    spl12_13 | spl12_1 | ~spl12_12),
% 33.84/4.64    inference(avatar_split_clause,[],[f408,f359,f182,f421])).
% 33.84/4.64  fof(f408,plain,(
% 33.84/4.64    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl12_1 | ~spl12_12)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f361,f125])).
% 33.84/4.64  fof(f125,plain,(
% 33.84/4.64    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f39])).
% 33.84/4.64  fof(f39,plain,(
% 33.84/4.64    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f38])).
% 33.84/4.64  fof(f38,plain,(
% 33.84/4.64    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f9])).
% 33.84/4.64  fof(f9,axiom,(
% 33.84/4.64    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 33.84/4.64  fof(f362,plain,(
% 33.84/4.64    spl12_12 | ~spl12_4),
% 33.84/4.64    inference(avatar_split_clause,[],[f287,f194,f359])).
% 33.84/4.64  fof(f287,plain,(
% 33.84/4.64    l1_lattices(sK0) | ~spl12_4),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f195,f113])).
% 33.84/4.64  fof(f113,plain,(
% 33.84/4.64    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f29])).
% 33.84/4.64  fof(f29,plain,(
% 33.84/4.64    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 33.84/4.64    inference(ennf_transformation,[],[f10])).
% 33.84/4.64  fof(f10,axiom,(
% 33.84/4.64    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 33.84/4.64  fof(f357,plain,(
% 33.84/4.64    spl12_11 | ~spl12_4),
% 33.84/4.64    inference(avatar_split_clause,[],[f288,f194,f354])).
% 33.84/4.64  fof(f288,plain,(
% 33.84/4.64    l2_lattices(sK0) | ~spl12_4),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f195,f114])).
% 33.84/4.64  fof(f114,plain,(
% 33.84/4.64    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f29])).
% 33.84/4.64  fof(f352,plain,(
% 33.84/4.64    spl12_10 | spl12_1 | ~spl12_2 | ~spl12_4),
% 33.84/4.64    inference(avatar_split_clause,[],[f289,f194,f186,f182,f349])).
% 33.84/4.64  fof(f289,plain,(
% 33.84/4.64    v4_lattices(sK0) | (spl12_1 | ~spl12_2 | ~spl12_4)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f187,f195,f116])).
% 33.84/4.64  fof(f116,plain,(
% 33.84/4.64    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f31])).
% 33.84/4.64  fof(f31,plain,(
% 33.84/4.64    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 33.84/4.64    inference(flattening,[],[f30])).
% 33.84/4.64  fof(f30,plain,(
% 33.84/4.64    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 33.84/4.64    inference(ennf_transformation,[],[f26])).
% 33.84/4.64  fof(f26,plain,(
% 33.84/4.64    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 33.84/4.64    inference(pure_predicate_removal,[],[f25])).
% 33.84/4.64  fof(f25,plain,(
% 33.84/4.64    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 33.84/4.64    inference(pure_predicate_removal,[],[f4])).
% 33.84/4.64  fof(f4,axiom,(
% 33.84/4.64    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 33.84/4.64  fof(f347,plain,(
% 33.84/4.64    spl12_9 | spl12_1 | ~spl12_2 | ~spl12_4),
% 33.84/4.64    inference(avatar_split_clause,[],[f290,f194,f186,f182,f344])).
% 33.84/4.64  fof(f290,plain,(
% 33.84/4.64    v6_lattices(sK0) | (spl12_1 | ~spl12_2 | ~spl12_4)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f187,f195,f117])).
% 33.84/4.64  fof(f117,plain,(
% 33.84/4.64    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f31])).
% 33.84/4.64  fof(f342,plain,(
% 33.84/4.64    spl12_8 | spl12_1 | ~spl12_2 | ~spl12_4),
% 33.84/4.64    inference(avatar_split_clause,[],[f291,f194,f186,f182,f339])).
% 33.84/4.64  fof(f291,plain,(
% 33.84/4.64    v8_lattices(sK0) | (spl12_1 | ~spl12_2 | ~spl12_4)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f187,f195,f118])).
% 33.84/4.64  fof(f118,plain,(
% 33.84/4.64    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f31])).
% 33.84/4.64  fof(f337,plain,(
% 33.84/4.64    spl12_7 | spl12_1 | ~spl12_2 | ~spl12_4),
% 33.84/4.64    inference(avatar_split_clause,[],[f292,f194,f186,f182,f334])).
% 33.84/4.64  fof(f292,plain,(
% 33.84/4.64    v9_lattices(sK0) | (spl12_1 | ~spl12_2 | ~spl12_4)),
% 33.84/4.64    inference(unit_resulting_resolution,[],[f183,f187,f195,f119])).
% 33.84/4.64  fof(f119,plain,(
% 33.84/4.64    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 33.84/4.64    inference(cnf_transformation,[],[f31])).
% 33.84/4.64  fof(f209,plain,(
% 33.84/4.64    ~spl12_1),
% 33.84/4.64    inference(avatar_split_clause,[],[f107,f182])).
% 33.84/4.64  fof(f107,plain,(
% 33.84/4.64    ~v2_struct_0(sK0)),
% 33.84/4.64    inference(cnf_transformation,[],[f69])).
% 33.84/4.64  fof(f69,plain,(
% 33.84/4.64    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 33.84/4.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f68])).
% 33.84/4.64  fof(f68,plain,(
% 33.84/4.64    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 33.84/4.64    introduced(choice_axiom,[])).
% 33.84/4.64  fof(f28,plain,(
% 33.84/4.64    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 33.84/4.64    inference(flattening,[],[f27])).
% 33.84/4.64  fof(f27,plain,(
% 33.84/4.64    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 33.84/4.64    inference(ennf_transformation,[],[f24])).
% 33.84/4.64  fof(f24,negated_conjecture,(
% 33.84/4.64    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 33.84/4.64    inference(negated_conjecture,[],[f23])).
% 33.84/4.64  fof(f23,conjecture,(
% 33.84/4.64    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 33.84/4.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 33.84/4.64  fof(f208,plain,(
% 33.84/4.64    spl12_2),
% 33.84/4.64    inference(avatar_split_clause,[],[f108,f186])).
% 33.84/4.64  fof(f108,plain,(
% 33.84/4.64    v10_lattices(sK0)),
% 33.84/4.64    inference(cnf_transformation,[],[f69])).
% 33.84/4.64  fof(f207,plain,(
% 33.84/4.64    spl12_6),
% 33.84/4.64    inference(avatar_split_clause,[],[f109,f204])).
% 33.84/4.64  fof(f109,plain,(
% 33.84/4.64    v4_lattice3(sK0)),
% 33.84/4.64    inference(cnf_transformation,[],[f69])).
% 33.84/4.64  fof(f202,plain,(
% 33.84/4.64    spl12_4),
% 33.84/4.64    inference(avatar_split_clause,[],[f110,f194])).
% 33.84/4.64  fof(f110,plain,(
% 33.84/4.64    l3_lattices(sK0)),
% 33.84/4.64    inference(cnf_transformation,[],[f69])).
% 33.84/4.64  fof(f201,plain,(
% 33.84/4.64    spl12_1 | ~spl12_2 | ~spl12_3 | ~spl12_4 | ~spl12_5),
% 33.84/4.64    inference(avatar_split_clause,[],[f111,f198,f194,f190,f186,f182])).
% 33.84/4.64  fof(f111,plain,(
% 33.84/4.64    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 33.84/4.64    inference(cnf_transformation,[],[f69])).
% 33.84/4.64  % SZS output end Proof for theBenchmark
% 33.84/4.64  % (9243)------------------------------
% 33.84/4.64  % (9243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.84/4.64  % (9243)Termination reason: Refutation
% 33.84/4.64  
% 33.84/4.64  % (9243)Memory used [KB]: 50276
% 33.84/4.64  % (9243)Time elapsed: 4.184 s
% 33.84/4.64  % (9243)------------------------------
% 33.84/4.64  % (9243)------------------------------
% 34.13/4.66  % (9217)Success in time 4.298 s
%------------------------------------------------------------------------------
