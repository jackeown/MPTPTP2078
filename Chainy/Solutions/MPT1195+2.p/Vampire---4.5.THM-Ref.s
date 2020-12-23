%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1195+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:11 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 281 expanded)
%              Number of leaves         :   14 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  326 (2361 expanded)
%              Number of equality atoms :   68 ( 494 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2459,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2399,f2400,f2453,f2458])).

fof(f2458,plain,
    ( ~ spl36_1
    | spl36_2 ),
    inference(avatar_contradiction_clause,[],[f2457])).

fof(f2457,plain,
    ( $false
    | ~ spl36_1
    | spl36_2 ),
    inference(subsumption_resolution,[],[f2455,f2398])).

fof(f2398,plain,
    ( sK1 != k2_lattices(sK0,sK1,sK2)
    | spl36_2 ),
    inference(avatar_component_clause,[],[f2396])).

fof(f2396,plain,
    ( spl36_2
  <=> sK1 = k2_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_2])])).

fof(f2455,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | ~ spl36_1 ),
    inference(backward_demodulation,[],[f2434,f2454])).

fof(f2454,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ spl36_1 ),
    inference(unit_resulting_resolution,[],[f2234,f2404,f2238,f2239,f2393,f2252])).

fof(f2252,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2164])).

fof(f2164,plain,(
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
    inference(nnf_transformation,[],[f2054])).

fof(f2054,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2053])).

fof(f2053,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2015])).

fof(f2015,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f2393,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ spl36_1 ),
    inference(avatar_component_clause,[],[f2392])).

fof(f2392,plain,
    ( spl36_1
  <=> r1_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl36_1])])).

fof(f2239,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2153,plain,
    ( ( sK1 != k2_lattices(sK0,sK1,sK2)
      | ~ r1_lattices(sK0,sK1,sK2) )
    & ( sK1 = k2_lattices(sK0,sK1,sK2)
      | r1_lattices(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2149,f2152,f2151,f2150])).

fof(f2150,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_lattices(X0,X1,X2) != X1
                  | ~ r1_lattices(X0,X1,X2) )
                & ( k2_lattices(X0,X1,X2) = X1
                  | r1_lattices(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(sK0,X1,X2) != X1
                | ~ r1_lattices(sK0,X1,X2) )
              & ( k2_lattices(sK0,X1,X2) = X1
                | r1_lattices(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2151,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_lattices(sK0,X1,X2) != X1
              | ~ r1_lattices(sK0,X1,X2) )
            & ( k2_lattices(sK0,X1,X2) = X1
              | r1_lattices(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( sK1 != k2_lattices(sK0,sK1,X2)
            | ~ r1_lattices(sK0,sK1,X2) )
          & ( sK1 = k2_lattices(sK0,sK1,X2)
            | r1_lattices(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2152,plain,
    ( ? [X2] :
        ( ( sK1 != k2_lattices(sK0,sK1,X2)
          | ~ r1_lattices(sK0,sK1,X2) )
        & ( sK1 = k2_lattices(sK0,sK1,X2)
          | r1_lattices(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( sK1 != k2_lattices(sK0,sK1,sK2)
        | ~ r1_lattices(sK0,sK1,sK2) )
      & ( sK1 = k2_lattices(sK0,sK1,sK2)
        | r1_lattices(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2149,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2148])).

fof(f2148,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_lattices(X0,X1,X2) != X1
                | ~ r1_lattices(X0,X1,X2) )
              & ( k2_lattices(X0,X1,X2) = X1
                | r1_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2044])).

fof(f2044,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2043])).

fof(f2043,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2041])).

fof(f2041,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f2040])).

fof(f2040,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f2238,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2404,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f2237,f2282])).

fof(f2282,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2081])).

fof(f2081,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2028])).

fof(f2028,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f2237,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2234,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2434,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f2234,f2237,f2236,f2238,f2239,f2248])).

fof(f2248,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2163])).

fof(f2163,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0)))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f2160,f2162,f2161])).

fof(f2161,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2162,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0)))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2160,plain,(
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
    inference(rectify,[],[f2159])).

fof(f2159,plain,(
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
    inference(nnf_transformation,[],[f2052])).

fof(f2052,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2051])).

fof(f2051,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2019])).

fof(f2019,axiom,(
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

fof(f2236,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2453,plain,
    ( spl36_1
    | ~ spl36_2 ),
    inference(avatar_contradiction_clause,[],[f2452])).

fof(f2452,plain,
    ( $false
    | spl36_1
    | ~ spl36_2 ),
    inference(subsumption_resolution,[],[f2451,f2437])).

fof(f2437,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ spl36_2 ),
    inference(forward_demodulation,[],[f2428,f2397])).

fof(f2397,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | ~ spl36_2 ),
    inference(avatar_component_clause,[],[f2396])).

fof(f2428,plain,(
    sK2 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f2234,f2237,f2235,f2238,f2239,f2244])).

fof(f2244,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2158])).

fof(f2158,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f2155,f2157,f2156])).

fof(f2156,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2157,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2155,plain,(
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
    inference(rectify,[],[f2154])).

fof(f2154,plain,(
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
    inference(nnf_transformation,[],[f2050])).

fof(f2050,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2049])).

fof(f2049,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2018])).

fof(f2018,axiom,(
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

fof(f2235,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2451,plain,
    ( sK2 != k1_lattices(sK0,sK1,sK2)
    | spl36_1 ),
    inference(unit_resulting_resolution,[],[f2234,f2404,f2238,f2239,f2394,f2253])).

fof(f2253,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2164])).

fof(f2394,plain,
    ( ~ r1_lattices(sK0,sK1,sK2)
    | spl36_1 ),
    inference(avatar_component_clause,[],[f2392])).

fof(f2400,plain,
    ( spl36_1
    | spl36_2 ),
    inference(avatar_split_clause,[],[f2240,f2396,f2392])).

fof(f2240,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f2153])).

fof(f2399,plain,
    ( ~ spl36_1
    | ~ spl36_2 ),
    inference(avatar_split_clause,[],[f2241,f2396,f2392])).

fof(f2241,plain,
    ( sK1 != k2_lattices(sK0,sK1,sK2)
    | ~ r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f2153])).
%------------------------------------------------------------------------------
