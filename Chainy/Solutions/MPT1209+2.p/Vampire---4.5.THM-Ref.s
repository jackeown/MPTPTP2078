%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1209+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:12 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
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
fof(f2879,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2389,f2402,f2407,f2465,f2872])).

fof(f2872,plain,
    ( ~ spl26_9
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(avatar_contradiction_clause,[],[f2871])).

fof(f2871,plain,
    ( $false
    | ~ spl26_9
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(subsumption_resolution,[],[f2870,f2196])).

fof(f2196,plain,(
    k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2133,plain,
    ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v14_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2069,f2132,f2131])).

fof(f2131,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v14_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2132,plain,
    ( ? [X1] :
        ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k6_lattices(sK0) != k3_lattices(sK0,k6_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2069,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2068])).

fof(f2068,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k6_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2062])).

fof(f2062,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f2061])).

fof(f2061,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k6_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_lattices)).

fof(f2870,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl26_9
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(forward_demodulation,[],[f2859,f2811])).

fof(f2811,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl26_9
    | ~ spl26_15 ),
    inference(forward_demodulation,[],[f2799,f2613])).

fof(f2613,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl26_9 ),
    inference(resolution,[],[f2504,f2195])).

fof(f2195,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2504,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0)) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2503,f2191])).

fof(f2191,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2503,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0))
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2502,f2354])).

fof(f2354,plain,
    ( l2_lattices(sK0)
    | ~ spl26_9 ),
    inference(avatar_component_clause,[],[f2353])).

fof(f2353,plain,
    ( spl26_9
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_9])])).

fof(f2502,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2496,f2193])).

fof(f2193,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2496,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0))
        | ~ v14_lattices(sK0)
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(resolution,[],[f2393,f2284])).

fof(f2284,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f2234])).

fof(f2234,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2169])).

fof(f2169,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK16(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK16(X0,X1)) != X1 )
                & m1_subset_1(sK16(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f2167,f2168])).

fof(f2168,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK16(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK16(X0,X1)) != X1 )
        & m1_subset_1(sK16(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2167,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f2166])).

fof(f2166,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2095])).

fof(f2095,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2094])).

fof(f2094,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2015])).

fof(f2015,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattices)).

fof(f2393,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2390,f2191])).

fof(f2390,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl26_9 ),
    inference(resolution,[],[f2354,f2237])).

fof(f2237,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2097])).

fof(f2097,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2096])).

fof(f2096,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2030])).

fof(f2030,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f2799,plain,
    ( k1_lattices(sK0,sK1,k6_lattices(sK0)) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl26_9
    | ~ spl26_15 ),
    inference(resolution,[],[f2631,f2393])).

fof(f2631,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,sK1,X0) = k3_lattices(sK0,sK1,X0) )
    | ~ spl26_15 ),
    inference(resolution,[],[f2401,f2195])).

fof(f2401,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl26_15 ),
    inference(avatar_component_clause,[],[f2400])).

fof(f2400,plain,
    ( spl26_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_15])])).

fof(f2859,plain,
    ( k3_lattices(sK0,k6_lattices(sK0),sK1) = k3_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl26_9
    | ~ spl26_16 ),
    inference(resolution,[],[f2649,f2393])).

fof(f2649,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k3_lattices(sK0,X0,sK1) = k3_lattices(sK0,sK1,X0) )
    | ~ spl26_16 ),
    inference(resolution,[],[f2406,f2195])).

fof(f2406,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X3,X2) = k3_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl26_16 ),
    inference(avatar_component_clause,[],[f2405])).

fof(f2405,plain,
    ( spl26_16
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,X3,X2) = k3_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_16])])).

fof(f2465,plain,(
    spl26_14 ),
    inference(avatar_contradiction_clause,[],[f2464])).

fof(f2464,plain,
    ( $false
    | spl26_14 ),
    inference(subsumption_resolution,[],[f2463,f2194])).

fof(f2194,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2463,plain,
    ( ~ l3_lattices(sK0)
    | spl26_14 ),
    inference(subsumption_resolution,[],[f2462,f2191])).

fof(f2462,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl26_14 ),
    inference(subsumption_resolution,[],[f2461,f2192])).

fof(f2192,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2461,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl26_14 ),
    inference(resolution,[],[f2398,f2272])).

fof(f2272,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2128])).

fof(f2128,plain,(
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
    inference(flattening,[],[f2127])).

fof(f2127,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f2398,plain,
    ( ~ v4_lattices(sK0)
    | spl26_14 ),
    inference(avatar_component_clause,[],[f2396])).

fof(f2396,plain,
    ( spl26_14
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_14])])).

fof(f2407,plain,
    ( ~ spl26_14
    | spl26_16
    | ~ spl26_9 ),
    inference(avatar_split_clause,[],[f2403,f2353,f2405,f2396])).

fof(f2403,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X3,X2) = k3_lattices(sK0,X2,X3)
        | ~ v4_lattices(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2392,f2191])).

fof(f2392,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X3,X2) = k3_lattices(sK0,X2,X3)
        | ~ v4_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(resolution,[],[f2354,f2215])).

fof(f2215,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2079])).

fof(f2079,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2078])).

fof(f2078,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2011])).

fof(f2011,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f2402,plain,
    ( ~ spl26_14
    | spl26_15
    | ~ spl26_9 ),
    inference(avatar_split_clause,[],[f2394,f2353,f2400,f2396])).

fof(f2394,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
        | ~ v4_lattices(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2391,f2191])).

fof(f2391,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
        | ~ v4_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(resolution,[],[f2354,f2216])).

fof(f2216,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2081])).

fof(f2081,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2080])).

fof(f2080,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2039])).

fof(f2039,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f2389,plain,(
    spl26_9 ),
    inference(avatar_contradiction_clause,[],[f2388])).

fof(f2388,plain,
    ( $false
    | spl26_9 ),
    inference(subsumption_resolution,[],[f2360,f2355])).

fof(f2355,plain,
    ( ~ l2_lattices(sK0)
    | spl26_9 ),
    inference(avatar_component_clause,[],[f2353])).

fof(f2360,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f2194,f2270])).

fof(f2270,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2126,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2066])).

fof(f2066,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2033])).

fof(f2033,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
%------------------------------------------------------------------------------
