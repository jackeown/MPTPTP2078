%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1197+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:11 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 381 expanded)
%              Number of leaves         :   23 ( 157 expanded)
%              Depth                    :   13
%              Number of atoms          :  455 (1515 expanded)
%              Number of equality atoms :   38 (  99 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2168,f2173,f2178,f2183,f2188,f2193,f2213,f2234,f2239,f2307,f2404,f2421])).

fof(f2421,plain,
    ( spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13
    | ~ spl16_14
    | spl16_15
    | ~ spl16_25 ),
    inference(avatar_contradiction_clause,[],[f2420])).

fof(f2420,plain,
    ( $false
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13
    | ~ spl16_14
    | spl16_15
    | ~ spl16_25 ),
    inference(subsumption_resolution,[],[f2419,f2167])).

% (2294)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
fof(f2167,plain,
    ( ~ v2_struct_0(sK0)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f2165])).

fof(f2165,plain,
    ( spl16_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f2419,plain,
    ( v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13
    | ~ spl16_14
    | spl16_15
    | ~ spl16_25 ),
    inference(subsumption_resolution,[],[f2418,f2238])).

fof(f2238,plain,
    ( l2_lattices(sK0)
    | ~ spl16_14 ),
    inference(avatar_component_clause,[],[f2236])).

fof(f2236,plain,
    ( spl16_14
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_14])])).

fof(f2418,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13
    | spl16_15
    | ~ spl16_25 ),
    inference(subsumption_resolution,[],[f2417,f2297])).

fof(f2297,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(backward_demodulation,[],[f2290,f2295])).

fof(f2295,plain,
    ( k2_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK1,sK2)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(backward_demodulation,[],[f2289,f2251])).

fof(f2251,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(unit_resulting_resolution,[],[f2167,f2172,f2192,f2187,f2233,f2130])).

fof(f2130,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2055])).

fof(f2055,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2054])).

fof(f2054,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2036])).

fof(f2036,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f2233,plain,
    ( l1_lattices(sK0)
    | ~ spl16_13 ),
    inference(avatar_component_clause,[],[f2231])).

fof(f2231,plain,
    ( spl16_13
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).

fof(f2187,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f2185])).

fof(f2185,plain,
    ( spl16_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f2192,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f2190])).

fof(f2190,plain,
    ( spl16_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f2172,plain,
    ( v6_lattices(sK0)
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f2170])).

fof(f2170,plain,
    ( spl16_2
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f2289,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(backward_demodulation,[],[f2262,f2253])).

fof(f2253,plain,
    ( k4_lattices(sK0,sK2,sK1) = k2_lattices(sK0,sK2,sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(unit_resulting_resolution,[],[f2167,f2172,f2187,f2192,f2233,f2130])).

fof(f2262,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(unit_resulting_resolution,[],[f2167,f2172,f2187,f2192,f2233,f2129])).

fof(f2129,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2053])).

fof(f2053,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2052])).

fof(f2052,plain,(
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

fof(f2290,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(backward_demodulation,[],[f2269,f2289])).

fof(f2269,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(unit_resulting_resolution,[],[f2167,f2172,f2192,f2187,f2233,f2131])).

fof(f2131,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2057])).

fof(f2057,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2056])).

fof(f2056,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2025])).

fof(f2025,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f2417,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_5
    | spl16_15
    | ~ spl16_25 ),
    inference(subsumption_resolution,[],[f2416,f2187])).

fof(f2416,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | spl16_15
    | ~ spl16_25 ),
    inference(subsumption_resolution,[],[f2413,f2306])).

fof(f2306,plain,
    ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK1)
    | spl16_15 ),
    inference(avatar_component_clause,[],[f2304])).

fof(f2304,plain,
    ( spl16_15
  <=> r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_15])])).

fof(f2413,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_25 ),
    inference(trivial_inequality_removal,[],[f2412])).

fof(f2412,plain,
    ( sK1 != sK1
    | r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl16_25 ),
    inference(superposition,[],[f2125,f2403])).

fof(f2403,plain,
    ( sK1 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK1)
    | ~ spl16_25 ),
    inference(avatar_component_clause,[],[f2401])).

fof(f2401,plain,
    ( spl16_25
  <=> sK1 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_25])])).

fof(f2125,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2087])).

fof(f2087,plain,(
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
    inference(nnf_transformation,[],[f2047])).

fof(f2047,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2046])).

fof(f2046,plain,(
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

fof(f2404,plain,
    ( spl16_25
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(avatar_split_clause,[],[f2329,f2231,f2190,f2185,f2180,f2175,f2170,f2165,f2401])).

fof(f2175,plain,
    ( spl16_3
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f2180,plain,
    ( spl16_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f2329,plain,
    ( sK1 = k1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_13 ),
    inference(forward_demodulation,[],[f2319,f2295])).

fof(f2319,plain,
    ( sK1 = k1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6 ),
    inference(unit_resulting_resolution,[],[f2167,f2182,f2177,f2192,f2187,f2139])).

fof(f2139,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2099])).

fof(f2099,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f2096,f2098,f2097])).

fof(f2097,plain,(
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

fof(f2098,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK6(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK7(X0) != k1_lattices(X0,k2_lattices(X0,sK6(X0),sK7(X0)),sK7(X0))
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2096,plain,(
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
    inference(rectify,[],[f2095])).

fof(f2095,plain,(
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
    inference(nnf_transformation,[],[f2066])).

fof(f2066,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2065])).

fof(f2065,plain,(
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

% (2299)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
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

fof(f2177,plain,
    ( v8_lattices(sK0)
    | ~ spl16_3 ),
    inference(avatar_component_clause,[],[f2175])).

fof(f2182,plain,
    ( l3_lattices(sK0)
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f2180])).

fof(f2307,plain,
    ( ~ spl16_15
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | spl16_10
    | ~ spl16_13 ),
    inference(avatar_split_clause,[],[f2296,f2231,f2210,f2190,f2185,f2170,f2165,f2304])).

fof(f2210,plain,
    ( spl16_10
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f2296,plain,
    ( ~ r1_lattices(sK0,k2_lattices(sK0,sK1,sK2),sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | spl16_10
    | ~ spl16_13 ),
    inference(backward_demodulation,[],[f2291,f2295])).

fof(f2291,plain,
    ( ~ r1_lattices(sK0,k2_lattices(sK0,sK2,sK1),sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_6
    | spl16_10
    | ~ spl16_13 ),
    inference(backward_demodulation,[],[f2212,f2289])).

fof(f2212,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    | spl16_10 ),
    inference(avatar_component_clause,[],[f2210])).

fof(f2239,plain,
    ( spl16_14
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f2227,f2180,f2236])).

fof(f2227,plain,
    ( l2_lattices(sK0)
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f2182,f2155])).

fof(f2155,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2073])).

fof(f2073,plain,(
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

fof(f2234,plain,
    ( spl16_13
    | ~ spl16_4 ),
    inference(avatar_split_clause,[],[f2225,f2180,f2231])).

fof(f2225,plain,
    ( l1_lattices(sK0)
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f2182,f2154])).

fof(f2154,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2073])).

fof(f2213,plain,(
    ~ spl16_10 ),
    inference(avatar_split_clause,[],[f2123,f2210])).

fof(f2123,plain,(
    ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f2086])).

fof(f2086,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2045,f2085,f2084,f2083])).

fof(f2083,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(sK0,k4_lattices(sK0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v8_lattices(sK0)
      & v6_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2084,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_lattices(sK0,k4_lattices(sK0,X1,X2),X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,X2),sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2085,plain,
    ( ? [X2] :
        ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,X2),sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2045,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2044])).

fof(f2044,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2043])).

fof(f2043,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f2042])).

fof(f2042,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(f2193,plain,(
    spl16_6 ),
    inference(avatar_split_clause,[],[f2122,f2190])).

fof(f2122,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2086])).

fof(f2188,plain,(
    spl16_5 ),
    inference(avatar_split_clause,[],[f2121,f2185])).

fof(f2121,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2086])).

fof(f2183,plain,(
    spl16_4 ),
    inference(avatar_split_clause,[],[f2120,f2180])).

fof(f2120,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2086])).

fof(f2178,plain,(
    spl16_3 ),
    inference(avatar_split_clause,[],[f2119,f2175])).

fof(f2119,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f2086])).

fof(f2173,plain,(
    spl16_2 ),
    inference(avatar_split_clause,[],[f2118,f2170])).

fof(f2118,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f2086])).

fof(f2168,plain,(
    ~ spl16_1 ),
    inference(avatar_split_clause,[],[f2117,f2165])).

fof(f2117,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2086])).
%------------------------------------------------------------------------------
