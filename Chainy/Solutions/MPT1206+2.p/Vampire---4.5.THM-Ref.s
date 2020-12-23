%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1206+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:12 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 217 expanded)
%              Number of leaves         :   14 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  356 (1081 expanded)
%              Number of equality atoms :   71 ( 199 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2877,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2405,f2414,f2419,f2424,f2870])).

fof(f2870,plain,
    ( ~ spl26_9
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(avatar_contradiction_clause,[],[f2869])).

fof(f2869,plain,
    ( $false
    | ~ spl26_9
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(subsumption_resolution,[],[f2868,f2194])).

fof(f2194,plain,(
    k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f2130])).

fof(f2130,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v13_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2062,f2129,f2128])).

fof(f2128,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v13_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2129,plain,
    ( ? [X1] :
        ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2062,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2061])).

fof(f2061,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2057])).

fof(f2057,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f2056])).

fof(f2056,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattices)).

fof(f2868,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl26_9
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(forward_demodulation,[],[f2857,f2807])).

fof(f2807,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,k5_lattices(sK0))
    | ~ spl26_9
    | ~ spl26_15 ),
    inference(forward_demodulation,[],[f2795,f2630])).

fof(f2630,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k5_lattices(sK0))
    | ~ spl26_9 ),
    inference(resolution,[],[f2493,f2193])).

fof(f2193,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2130])).

fof(f2493,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2492,f2189])).

fof(f2189,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2130])).

fof(f2492,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2491,f2355])).

fof(f2355,plain,
    ( l1_lattices(sK0)
    | ~ spl26_9 ),
    inference(avatar_component_clause,[],[f2354])).

fof(f2354,plain,
    ( spl26_9
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_9])])).

fof(f2491,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2486,f2191])).

fof(f2191,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f2130])).

fof(f2486,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(resolution,[],[f2409,f2285])).

fof(f2285,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f2234])).

fof(f2234,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2166])).

fof(f2166,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f2164,f2165])).

fof(f2165,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK16(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK16(X0,X1)) != X1 )
        & m1_subset_1(sK16(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2164,plain,(
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
    inference(rectify,[],[f2163])).

fof(f2163,plain,(
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
    inference(nnf_transformation,[],[f2092])).

fof(f2092,plain,(
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
    inference(flattening,[],[f2091])).

fof(f2091,plain,(
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

fof(f2409,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2406,f2189])).

fof(f2406,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl26_9 ),
    inference(resolution,[],[f2355,f2237])).

fof(f2237,plain,(
    ! [X0] :
      ( ~ l1_lattices(X0)
      | m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2094])).

fof(f2094,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2093])).

fof(f2093,plain,(
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

fof(f2795,plain,
    ( k2_lattices(sK0,sK1,k5_lattices(sK0)) = k4_lattices(sK0,sK1,k5_lattices(sK0))
    | ~ spl26_9
    | ~ spl26_15 ),
    inference(resolution,[],[f2648,f2409])).

fof(f2648,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,X0) = k4_lattices(sK0,sK1,X0) )
    | ~ spl26_15 ),
    inference(resolution,[],[f2413,f2193])).

fof(f2413,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X1,X0) = k2_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl26_15 ),
    inference(avatar_component_clause,[],[f2412])).

fof(f2412,plain,
    ( spl26_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X1,X0) = k2_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_15])])).

fof(f2857,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k5_lattices(sK0))
    | ~ spl26_9
    | ~ spl26_16 ),
    inference(resolution,[],[f2666,f2409])).

fof(f2666,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,sK1) = k4_lattices(sK0,sK1,X0) )
    | ~ spl26_16 ),
    inference(resolution,[],[f2418,f2193])).

fof(f2418,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k4_lattices(sK0,X3,X2) = k4_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl26_16 ),
    inference(avatar_component_clause,[],[f2417])).

fof(f2417,plain,
    ( spl26_16
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k4_lattices(sK0,X3,X2) = k4_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_16])])).

fof(f2424,plain,(
    spl26_11 ),
    inference(avatar_contradiction_clause,[],[f2423])).

fof(f2423,plain,
    ( $false
    | spl26_11 ),
    inference(subsumption_resolution,[],[f2422,f2192])).

fof(f2192,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2130])).

fof(f2422,plain,
    ( ~ l3_lattices(sK0)
    | spl26_11 ),
    inference(subsumption_resolution,[],[f2421,f2189])).

fof(f2421,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl26_11 ),
    inference(subsumption_resolution,[],[f2420,f2190])).

fof(f2190,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2130])).

fof(f2420,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl26_11 ),
    inference(resolution,[],[f2371,f2275])).

fof(f2275,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2125])).

fof(f2125,plain,(
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
    inference(flattening,[],[f2124])).

fof(f2124,plain,(
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

fof(f2371,plain,
    ( ~ v6_lattices(sK0)
    | spl26_11 ),
    inference(avatar_component_clause,[],[f2369])).

fof(f2369,plain,
    ( spl26_11
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_11])])).

fof(f2419,plain,
    ( ~ spl26_11
    | spl26_16
    | ~ spl26_9 ),
    inference(avatar_split_clause,[],[f2415,f2354,f2417,f2369])).

fof(f2415,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k4_lattices(sK0,X3,X2) = k4_lattices(sK0,X2,X3)
        | ~ v6_lattices(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2408,f2189])).

fof(f2408,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k4_lattices(sK0,X3,X2) = k4_lattices(sK0,X2,X3)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(resolution,[],[f2355,f2213])).

fof(f2213,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2072])).

fof(f2072,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2071])).

fof(f2071,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2012])).

fof(f2012,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f2414,plain,
    ( ~ spl26_11
    | spl26_15
    | ~ spl26_9 ),
    inference(avatar_split_clause,[],[f2410,f2354,f2412,f2369])).

fof(f2410,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X1,X0) = k2_lattices(sK0,X1,X0)
        | ~ v6_lattices(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2407,f2189])).

fof(f2407,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X1,X0) = k2_lattices(sK0,X1,X0)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(resolution,[],[f2355,f2214])).

fof(f2214,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2074])).

fof(f2074,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2073])).

fof(f2073,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2039])).

fof(f2039,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f2405,plain,(
    spl26_9 ),
    inference(avatar_contradiction_clause,[],[f2404])).

fof(f2404,plain,
    ( $false
    | spl26_9 ),
    inference(subsumption_resolution,[],[f2361,f2356])).

fof(f2356,plain,
    ( ~ l1_lattices(sK0)
    | spl26_9 ),
    inference(avatar_component_clause,[],[f2354])).

fof(f2361,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f2192,f2271])).

fof(f2271,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2123])).

fof(f2123,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2059])).

fof(f2059,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2031])).

fof(f2031,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
%------------------------------------------------------------------------------
