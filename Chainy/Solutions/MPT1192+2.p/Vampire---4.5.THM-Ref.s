%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1192+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:11 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 396 expanded)
%              Number of leaves         :   13 ( 134 expanded)
%              Depth                    :   17
%              Number of atoms          :  298 (2428 expanded)
%              Number of equality atoms :   59 ( 396 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2699,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2698,f2181])).

fof(f2181,plain,(
    sK1 != k1_lattices(sK0,sK1,sK1) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2116,plain,
    ( sK1 != k1_lattices(sK0,sK1,sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2032,f2115,f2114])).

fof(f2114,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_lattices(X0,X1,X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_lattices(sK0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & v6_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2115,plain,
    ( ? [X1] :
        ( k1_lattices(sK0,X1,X1) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k1_lattices(sK0,sK1,sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2032,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2031])).

fof(f2031,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2030])).

fof(f2030,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_lattices(X0,X1,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f2029])).

fof(f2029,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

fof(f2698,plain,(
    sK1 = k1_lattices(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f2646,f2693])).

fof(f2693,plain,(
    sK1 = k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f2650,f2683])).

fof(f2683,plain,(
    sK1 = k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f2662,f2352])).

fof(f2352,plain,(
    sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f2351,f2175])).

fof(f2175,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2351,plain,
    ( sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2350,f2176])).

fof(f2176,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2350,plain,
    ( sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2349,f2297])).

fof(f2297,plain,(
    l1_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f2179,f2208])).

fof(f2208,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2057])).

fof(f2057,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2021])).

fof(f2021,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f2179,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2349,plain,
    ( sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2348,f2180])).

fof(f2180,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2348,plain,
    ( sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2344,f2343])).

fof(f2343,plain,(
    m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f2175,f2180,f2180,f2298,f2182])).

fof(f2182,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2034,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2033])).

fof(f2033,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2015])).

fof(f2015,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(f2298,plain,(
    l2_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f2179,f2209])).

fof(f2209,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2057])).

fof(f2344,plain,
    ( sK1 = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | ~ m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f2304,f2218])).

fof(f2218,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2063])).

fof(f2063,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2062])).

fof(f2062,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2028])).

fof(f2028,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f2304,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f2175,f2179,f2178,f2180,f2180,f2210])).

fof(f2210,plain,(
    ! [X4,X0,X3] :
      ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2140])).

fof(f2140,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),sK10(X0)))
            & m1_subset_1(sK10(X0),u1_struct_0(X0))
            & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f2137,f2139,f2138])).

fof(f2138,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK9(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2139,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK9(X0) != k2_lattices(X0,sK9(X0),k1_lattices(X0,sK9(X0),sK10(X0)))
        & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2137,plain,(
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
    inference(rectify,[],[f2136])).

fof(f2136,plain,(
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
    inference(nnf_transformation,[],[f2059])).

fof(f2059,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2058])).

fof(f2058,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2013])).

fof(f2013,axiom,(
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

fof(f2178,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2662,plain,(
    k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f2175,f2176,f2297,f2180,f2343,f2219])).

fof(f2219,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2065])).

fof(f2065,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2064])).

fof(f2064,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2009])).

fof(f2009,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f2650,plain,(
    k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f2175,f2176,f2297,f2180,f2343,f2218])).

fof(f2646,plain,(
    sK1 = k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f2175,f2179,f2177,f2180,f2343,f2214])).

fof(f2214,plain,(
    ! [X4,X0,X3] :
      ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2145])).

fof(f2145,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK12(X0) != k1_lattices(X0,k2_lattices(X0,sK11(X0),sK12(X0)),sK12(X0))
            & m1_subset_1(sK12(X0),u1_struct_0(X0))
            & m1_subset_1(sK11(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f2142,f2144,f2143])).

fof(f2143,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK11(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK11(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2144,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK11(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK12(X0) != k1_lattices(X0,k2_lattices(X0,sK11(X0),sK12(X0)),sK12(X0))
        & m1_subset_1(sK12(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2142,plain,(
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
    inference(rectify,[],[f2141])).

fof(f2141,plain,(
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
    inference(nnf_transformation,[],[f2061])).

fof(f2061,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2060])).

fof(f2060,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2012])).

fof(f2012,axiom,(
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

fof(f2177,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f2116])).
%------------------------------------------------------------------------------
