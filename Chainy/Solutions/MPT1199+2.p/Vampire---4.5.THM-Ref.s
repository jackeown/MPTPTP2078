%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1199+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:11 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 286 expanded)
%              Number of leaves         :    7 ( 109 expanded)
%              Depth                    :   14
%              Number of atoms          :  221 (2166 expanded)
%              Number of equality atoms :   50 ( 340 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2375,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2373,f2145])).

fof(f2145,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f2100])).

fof(f2100,plain,
    ( sK1 != sK2
    & r1_lattices(sK0,sK2,sK1)
    & r1_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l2_lattices(sK0)
    & v4_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2056,f2099,f2098,f2097])).

fof(f2097,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r1_lattices(X0,X2,X1)
                & r1_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(sK0,X2,X1)
              & r1_lattices(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l2_lattices(sK0)
      & v4_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2098,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r1_lattices(sK0,X2,X1)
            & r1_lattices(sK0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & r1_lattices(sK0,X2,sK1)
          & r1_lattices(sK0,sK1,X2)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2099,plain,
    ( ? [X2] :
        ( sK1 != X2
        & r1_lattices(sK0,X2,sK1)
        & r1_lattices(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK1 != sK2
      & r1_lattices(sK0,sK2,sK1)
      & r1_lattices(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2056,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(X0,X2,X1)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v4_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2055])).

fof(f2055,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(X0,X2,X1)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v4_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2045])).

fof(f2045,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f2044])).

fof(f2044,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(f2373,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f2347,f2363])).

fof(f2363,plain,(
    sK1 = k3_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f2352,f2293])).

fof(f2293,plain,(
    sK1 = k1_lattices(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f2292,f2142])).

fof(f2142,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2100])).

fof(f2292,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f2289,f2141])).

fof(f2141,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2100])).

fof(f2289,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f2219,f2144])).

fof(f2144,plain,(
    r1_lattices(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f2100])).

fof(f2219,plain,(
    ! [X4,X3] :
      ( ~ r1_lattices(sK0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k1_lattices(sK0,X3,X4) = X4 ) ),
    inference(subsumption_resolution,[],[f2208,f2138])).

fof(f2138,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2100])).

fof(f2208,plain,(
    ! [X4,X3] :
      ( ~ r1_lattices(sK0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k1_lattices(sK0,X3,X4) = X4
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2140,f2164])).

fof(f2164,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2120])).

fof(f2120,plain,(
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
    inference(nnf_transformation,[],[f2066])).

fof(f2066,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2065])).

fof(f2065,plain,(
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

fof(f2140,plain,(
    l2_lattices(sK0) ),
    inference(cnf_transformation,[],[f2100])).

fof(f2352,plain,(
    k3_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f2246,f2141])).

fof(f2246,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | k3_lattices(sK0,sK2,X7) = k1_lattices(sK0,sK2,X7) ) ),
    inference(resolution,[],[f2206,f2142])).

fof(f2206,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k3_lattices(sK0,X3,X2) = k1_lattices(sK0,X3,X2) ) ),
    inference(global_subsumption,[],[f2140,f2205])).

fof(f2205,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | k3_lattices(sK0,X3,X2) = k1_lattices(sK0,X3,X2) ) ),
    inference(subsumption_resolution,[],[f2202,f2138])).

fof(f2202,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | k3_lattices(sK0,X3,X2) = k1_lattices(sK0,X3,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2139,f2194])).

fof(f2194,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2092])).

fof(f2092,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2091])).

fof(f2091,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2034])).

fof(f2034,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f2139,plain,(
    v4_lattices(sK0) ),
    inference(cnf_transformation,[],[f2100])).

fof(f2347,plain,(
    sK2 = k3_lattices(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f2268,f2337])).

fof(f2337,plain,(
    sK2 = k3_lattices(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f2327,f2291])).

fof(f2291,plain,(
    sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f2290,f2141])).

fof(f2290,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f2288,f2142])).

fof(f2288,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f2219,f2143])).

fof(f2143,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f2100])).

fof(f2327,plain,(
    k3_lattices(sK0,sK1,sK2) = k1_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f2245,f2142])).

fof(f2245,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k3_lattices(sK0,sK1,X6) = k1_lattices(sK0,sK1,X6) ) ),
    inference(resolution,[],[f2206,f2141])).

fof(f2268,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f2223,f2142])).

fof(f2223,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k3_lattices(sK0,sK1,X6) = k3_lattices(sK0,X6,sK1) ) ),
    inference(resolution,[],[f2204,f2141])).

fof(f2204,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_lattices(sK0,X1,X0) = k3_lattices(sK0,X0,X1) ) ),
    inference(global_subsumption,[],[f2140,f2203])).

fof(f2203,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | k3_lattices(sK0,X1,X0) = k3_lattices(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f2201,f2138])).

fof(f2201,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | k3_lattices(sK0,X1,X0) = k3_lattices(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2139,f2195])).

fof(f2195,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2094])).

fof(f2094,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2093])).

fof(f2093,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
%------------------------------------------------------------------------------
