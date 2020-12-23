%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1208+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:12 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 320 expanded)
%              Number of leaves         :   17 ( 101 expanded)
%              Depth                    :   19
%              Number of atoms          :  445 (1647 expanded)
%              Number of equality atoms :   91 ( 300 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3535,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2405,f2414,f2419,f2424,f3524])).

fof(f3524,plain,
    ( ~ spl26_9
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(avatar_contradiction_clause,[],[f3523])).

fof(f3523,plain,
    ( $false
    | ~ spl26_9
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(subsumption_resolution,[],[f3522,f2197])).

fof(f2197,plain,(
    sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2133,plain,
    ( sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v14_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2067,f2132,f2131])).

fof(f2131,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_lattices(X0,k6_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k4_lattices(sK0,k6_lattices(sK0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v14_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2132,plain,
    ( ? [X1] :
        ( k4_lattices(sK0,k6_lattices(sK0),X1) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k4_lattices(sK0,k6_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2067,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2066])).

fof(f2066,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v14_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2061])).

fof(f2061,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f2060])).

fof(f2060,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(f3522,plain,
    ( sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)
    | ~ spl26_9
    | ~ spl26_15
    | ~ spl26_16 ),
    inference(forward_demodulation,[],[f3510,f2826])).

fof(f2826,plain,
    ( sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl26_9
    | ~ spl26_15 ),
    inference(forward_demodulation,[],[f2814,f2787])).

fof(f2787,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl26_9 ),
    inference(forward_demodulation,[],[f2775,f2645])).

fof(f2645,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl26_9 ),
    inference(resolution,[],[f2432,f2196])).

fof(f2196,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2432,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0)) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2431,f2192])).

fof(f2192,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2431,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0))
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2430,f2354])).

fof(f2354,plain,
    ( l2_lattices(sK0)
    | ~ spl26_9 ),
    inference(avatar_component_clause,[],[f2353])).

fof(f2353,plain,
    ( spl26_9
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_9])])).

fof(f2430,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2426,f2194])).

fof(f2194,plain,(
    v14_lattices(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2426,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k6_lattices(sK0) = k1_lattices(sK0,X1,k6_lattices(sK0))
        | ~ v14_lattices(sK0)
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl26_9 ),
    inference(resolution,[],[f2407,f2288])).

fof(f2288,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f2237])).

fof(f2237,plain,(
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
    inference(nnf_transformation,[],[f2097])).

fof(f2097,plain,(
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
    inference(flattening,[],[f2096])).

fof(f2096,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattices)).

fof(f2407,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl26_9 ),
    inference(subsumption_resolution,[],[f2406,f2192])).

fof(f2406,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl26_9 ),
    inference(resolution,[],[f2354,f2240])).

fof(f2240,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2099])).

fof(f2099,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2098])).

fof(f2098,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f2775,plain,
    ( sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,k6_lattices(sK0)))
    | ~ spl26_9 ),
    inference(resolution,[],[f2591,f2407])).

fof(f2591,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,X0)) ) ),
    inference(resolution,[],[f2395,f2196])).

fof(f2395,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | k2_lattices(sK0,X6,k1_lattices(sK0,X6,X5)) = X6 ) ),
    inference(subsumption_resolution,[],[f2394,f2192])).

fof(f2394,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k2_lattices(sK0,X6,k1_lattices(sK0,X6,X5)) = X6
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2379,f2195])).

fof(f2195,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2379,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k2_lattices(sK0,X6,k1_lattices(sK0,X6,X5)) = X6
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2349,f2266])).

fof(f2266,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2190])).

fof(f2190,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK24(X0) != k2_lattices(X0,sK24(X0),k1_lattices(X0,sK24(X0),sK25(X0)))
            & m1_subset_1(sK25(X0),u1_struct_0(X0))
            & m1_subset_1(sK24(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24,sK25])],[f2187,f2189,f2188])).

fof(f2188,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK24(X0) != k2_lattices(X0,sK24(X0),k1_lattices(X0,sK24(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK24(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2189,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK24(X0) != k2_lattices(X0,sK24(X0),k1_lattices(X0,sK24(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK24(X0) != k2_lattices(X0,sK24(X0),k1_lattices(X0,sK24(X0),sK25(X0)))
        & m1_subset_1(sK25(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2187,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f2186])).

fof(f2186,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2121])).

fof(f2121,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2120])).

fof(f2120,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2022])).

fof(f2022,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f2349,plain,(
    v9_lattices(sK0) ),
    inference(global_subsumption,[],[f2195,f2348])).

fof(f2348,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f2297,f2192])).

fof(f2297,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f2193,f2281])).

fof(f2281,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v9_lattices(X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f2193,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2133])).

fof(f2814,plain,
    ( k4_lattices(sK0,sK1,k6_lattices(sK0)) = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl26_9
    | ~ spl26_15 ),
    inference(resolution,[],[f2627,f2407])).

fof(f2627,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1,X0) = k4_lattices(sK0,sK1,X0) )
    | ~ spl26_15 ),
    inference(resolution,[],[f2413,f2196])).

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

fof(f3510,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | ~ spl26_9
    | ~ spl26_16 ),
    inference(resolution,[],[f2663,f2407])).

fof(f2663,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,sK1) = k4_lattices(sK0,sK1,X0) )
    | ~ spl26_16 ),
    inference(resolution,[],[f2418,f2196])).

% (30855)ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_18 on theBenchmark
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
    inference(subsumption_resolution,[],[f2422,f2195])).

fof(f2422,plain,
    ( ~ l3_lattices(sK0)
    | spl26_11 ),
    inference(subsumption_resolution,[],[f2421,f2192])).

fof(f2421,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl26_11 ),
    inference(subsumption_resolution,[],[f2420,f2193])).

fof(f2420,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl26_11 ),
    inference(resolution,[],[f2370,f2278])).

fof(f2278,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2128])).

fof(f2370,plain,
    ( ~ v6_lattices(sK0)
    | spl26_11 ),
    inference(avatar_component_clause,[],[f2368])).

fof(f2368,plain,
    ( spl26_11
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl26_11])])).

fof(f2419,plain,
    ( ~ spl26_11
    | spl26_16 ),
    inference(avatar_split_clause,[],[f2415,f2417,f2368])).

fof(f2415,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k4_lattices(sK0,X3,X2) = k4_lattices(sK0,X2,X3)
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f2409,f2192])).

fof(f2409,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k4_lattices(sK0,X3,X2) = k4_lattices(sK0,X2,X3)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2360,f2216])).

fof(f2216,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2077])).

fof(f2077,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2076])).

fof(f2076,plain,(
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

fof(f2360,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f2195,f2273])).

fof(f2273,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2126,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2033])).

fof(f2033,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f2414,plain,
    ( ~ spl26_11
    | spl26_15 ),
    inference(avatar_split_clause,[],[f2410,f2412,f2368])).

fof(f2410,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,X1,X0) = k2_lattices(sK0,X1,X0)
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f2408,f2192])).

fof(f2408,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k4_lattices(sK0,X1,X0) = k2_lattices(sK0,X1,X0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2360,f2217])).

fof(f2217,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2079])).

fof(f2079,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2078])).

fof(f2078,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2041])).

fof(f2041,axiom,(
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
    inference(subsumption_resolution,[],[f2403,f2195])).

fof(f2403,plain,
    ( ~ l3_lattices(sK0)
    | spl26_9 ),
    inference(resolution,[],[f2355,f2274])).

fof(f2274,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2355,plain,
    ( ~ l2_lattices(sK0)
    | spl26_9 ),
    inference(avatar_component_clause,[],[f2353])).
%------------------------------------------------------------------------------
