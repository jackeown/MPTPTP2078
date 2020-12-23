%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1205+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:12 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 262 expanded)
%              Number of leaves         :   15 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :  392 (1370 expanded)
%              Number of equality atoms :   80 ( 252 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2398,f2411,f2426,f3118])).

fof(f3118,plain,
    ( ~ spl26_9
    | ~ spl26_16 ),
    inference(avatar_contradiction_clause,[],[f3117])).

fof(f3117,plain,
    ( $false
    | ~ spl26_9
    | ~ spl26_16 ),
    inference(subsumption_resolution,[],[f3116,f2190])).

fof(f2190,plain,(
    sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2126,plain,
    ( sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v13_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2060,f2125,f2124])).

fof(f2124,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_lattices(X0,k5_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k3_lattices(sK0,k5_lattices(sK0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v13_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2125,plain,
    ( ? [X1] :
        ( k3_lattices(sK0,k5_lattices(sK0),X1) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2060,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2059])).

fof(f2059,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2056])).

fof(f2056,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f2055])).

fof(f2055,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

fof(f3116,plain,
    ( sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl26_9
    | ~ spl26_16 ),
    inference(forward_demodulation,[],[f3104,f3090])).

fof(f3090,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl26_9 ),
    inference(forward_demodulation,[],[f3078,f2565])).

fof(f2565,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl26_9 ),
    inference(resolution,[],[f2483,f2189])).

fof(f2189,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2483,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2482,f2185])).

fof(f2185,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2482,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2481,f2347])).

fof(f2347,plain,
    ( l1_lattices(sK0)
    | ~ spl26_9 ),
    inference(avatar_component_clause,[],[f2346])).

fof(f2346,plain,
    ( spl26_9
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_9])])).

fof(f2481,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2478,f2187])).

fof(f2187,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2478,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(resolution,[],[f2400,f2282])).

fof(f2282,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f2227])).

fof(f2227,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2162])).

fof(f2162,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK16(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK16(X0,X1)) != X1 )
                & m1_subset_1(sK16(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f2160,f2161])).

fof(f2161,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK16(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK16(X0,X1)) != X1 )
        & m1_subset_1(sK16(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2160,plain,(
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
    inference(rectify,[],[f2159])).

fof(f2159,plain,(
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
    inference(nnf_transformation,[],[f2086])).

fof(f2086,plain,(
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
    inference(flattening,[],[f2085])).

fof(f2085,plain,(
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
    inference(ennf_transformation,[],[f2014])).

fof(f2014,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f2400,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2399,f2185])).

fof(f2399,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl26_9 ),
    inference(resolution,[],[f2347,f2231])).

fof(f2231,plain,(
    ! [X0] :
      ( ~ l1_lattices(X0)
      | m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2088])).

fof(f2088,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2087])).

fof(f2087,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2028])).

fof(f2028,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f3078,plain,
    ( sK1 = k1_lattices(sK0,k2_lattices(sK0,k5_lattices(sK0),sK1),sK1)
    | ~ spl26_9 ),
    inference(resolution,[],[f2548,f2189])).

fof(f2548,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,k5_lattices(sK0),X1),X1) = X1 )
    | ~ spl26_9 ),
    inference(resolution,[],[f2367,f2400])).

fof(f2367,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X3,X2),X2) = X2 ) ),
    inference(subsumption_resolution,[],[f2366,f2185])).

fof(f2366,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X3,X2),X2) = X2
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2355,f2188])).

fof(f2188,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2355,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X3,X2),X2) = X2
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2340,f2253])).

fof(f2253,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2178])).

fof(f2178,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK23(X0) != k1_lattices(X0,k2_lattices(X0,sK22(X0),sK23(X0)),sK23(X0))
            & m1_subset_1(sK23(X0),u1_struct_0(X0))
            & m1_subset_1(sK22(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22,sK23])],[f2175,f2177,f2176])).

fof(f2176,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK22(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK22(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2177,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK22(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK23(X0) != k1_lattices(X0,k2_lattices(X0,sK22(X0),sK23(X0)),sK23(X0))
        & m1_subset_1(sK23(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2175,plain,(
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
    inference(rectify,[],[f2174])).

fof(f2174,plain,(
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
    inference(nnf_transformation,[],[f2108])).

fof(f2108,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2107])).

fof(f2107,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2020])).

fof(f2020,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f2340,plain,(
    v8_lattices(sK0) ),
    inference(global_subsumption,[],[f2188,f2339])).

fof(f2339,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f2289,f2185])).

fof(f2289,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f2186,f2273])).

fof(f2273,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2121,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f2120])).

fof(f2120,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2009])).

fof(f2009,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f2186,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2126])).

fof(f3104,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl26_9
    | ~ spl26_16 ),
    inference(resolution,[],[f2602,f2189])).

fof(f2602,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k3_lattices(sK0,k5_lattices(sK0),X1) = k1_lattices(sK0,k5_lattices(sK0),X1) )
    | ~ spl26_9
    | ~ spl26_16 ),
    inference(resolution,[],[f2410,f2400])).

fof(f2410,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl26_16 ),
    inference(avatar_component_clause,[],[f2409])).

fof(f2409,plain,
    ( spl26_16
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_16])])).

fof(f2426,plain,(
    spl26_15 ),
    inference(avatar_contradiction_clause,[],[f2425])).

fof(f2425,plain,
    ( $false
    | spl26_15 ),
    inference(subsumption_resolution,[],[f2424,f2188])).

fof(f2424,plain,
    ( ~ l3_lattices(sK0)
    | spl26_15 ),
    inference(subsumption_resolution,[],[f2423,f2185])).

fof(f2423,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl26_15 ),
    inference(subsumption_resolution,[],[f2422,f2186])).

fof(f2422,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl26_15 ),
    inference(resolution,[],[f2407,f2269])).

fof(f2269,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2121])).

fof(f2407,plain,
    ( ~ v4_lattices(sK0)
    | spl26_15 ),
    inference(avatar_component_clause,[],[f2405])).

fof(f2405,plain,
    ( spl26_15
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_15])])).

fof(f2411,plain,
    ( ~ spl26_15
    | spl26_16 ),
    inference(avatar_split_clause,[],[f2403,f2409,f2405])).

fof(f2403,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
      | ~ v4_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f2401,f2185])).

fof(f2401,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2353,f2210])).

fof(f2210,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2072])).

fof(f2072,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2071])).

fof(f2071,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2037])).

fof(f2037,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f2353,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f2188,f2267])).

fof(f2267,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2119])).

fof(f2119,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2031])).

fof(f2031,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f2398,plain,(
    spl26_9 ),
    inference(avatar_contradiction_clause,[],[f2397])).

fof(f2397,plain,
    ( $false
    | spl26_9 ),
    inference(subsumption_resolution,[],[f2396,f2188])).

fof(f2396,plain,
    ( ~ l3_lattices(sK0)
    | spl26_9 ),
    inference(resolution,[],[f2348,f2266])).

fof(f2266,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2119])).

fof(f2348,plain,
    ( ~ l1_lattices(sK0)
    | spl26_9 ),
    inference(avatar_component_clause,[],[f2346])).
%------------------------------------------------------------------------------
