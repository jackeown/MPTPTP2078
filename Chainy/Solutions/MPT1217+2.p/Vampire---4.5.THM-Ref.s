%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1217+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 6.88s
% Output     : Refutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :   92 (1108 expanded)
%              Number of leaves         :   15 ( 434 expanded)
%              Depth                    :   15
%              Number of atoms          :  429 (8053 expanded)
%              Number of equality atoms :   31 (  31 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14673,plain,(
    $false ),
    inference(global_subsumption,[],[f12186,f10864])).

% (25126)Termination reason: Time limit

% (25126)Memory used [KB]: 17270
% (25126)Time elapsed: 0.822 s
% (25126)------------------------------
% (25126)------------------------------
fof(f10864,plain,(
    ~ r1_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28)) ),
    inference(unit_resulting_resolution,[],[f2437,f2777,f2779,f2780,f2440,f2793,f2444,f3002,f2454])).

fof(f2454,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2305])).

fof(f2305,plain,(
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
    inference(nnf_transformation,[],[f2097])).

fof(f2097,plain,(
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
    inference(flattening,[],[f2096])).

fof(f2096,plain,(
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
    inference(ennf_transformation,[],[f2050])).

fof(f2050,axiom,(
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

fof(f3002,plain,(
    m1_subset_1(k7_lattices(sK27,sK29),u1_struct_0(sK27)) ),
    inference(unit_resulting_resolution,[],[f2437,f2440,f2442,f2445])).

fof(f2445,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2083])).

fof(f2083,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2082])).

fof(f2082,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2038])).

fof(f2038,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f2442,plain,(
    m1_subset_1(sK29,u1_struct_0(sK27)) ),
    inference(cnf_transformation,[],[f2303])).

fof(f2303,plain,
    ( ~ r3_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28))
    & r3_lattices(sK27,sK28,sK29)
    & m1_subset_1(sK29,u1_struct_0(sK27))
    & m1_subset_1(sK28,u1_struct_0(sK27))
    & l3_lattices(sK27)
    & v17_lattices(sK27)
    & v10_lattices(sK27)
    & ~ v2_struct_0(sK27) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27,sK28,sK29])],[f2081,f2302,f2301,f2300])).

fof(f2300,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK27,k7_lattices(sK27,X2),k7_lattices(sK27,X1))
              & r3_lattices(sK27,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK27)) )
          & m1_subset_1(X1,u1_struct_0(sK27)) )
      & l3_lattices(sK27)
      & v17_lattices(sK27)
      & v10_lattices(sK27)
      & ~ v2_struct_0(sK27) ) ),
    introduced(choice_axiom,[])).

fof(f2301,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r3_lattices(sK27,k7_lattices(sK27,X2),k7_lattices(sK27,X1))
            & r3_lattices(sK27,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK27)) )
        & m1_subset_1(X1,u1_struct_0(sK27)) )
   => ( ? [X2] :
          ( ~ r3_lattices(sK27,k7_lattices(sK27,X2),k7_lattices(sK27,sK28))
          & r3_lattices(sK27,sK28,X2)
          & m1_subset_1(X2,u1_struct_0(sK27)) )
      & m1_subset_1(sK28,u1_struct_0(sK27)) ) ),
    introduced(choice_axiom,[])).

fof(f2302,plain,
    ( ? [X2] :
        ( ~ r3_lattices(sK27,k7_lattices(sK27,X2),k7_lattices(sK27,sK28))
        & r3_lattices(sK27,sK28,X2)
        & m1_subset_1(X2,u1_struct_0(sK27)) )
   => ( ~ r3_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28))
      & r3_lattices(sK27,sK28,sK29)
      & m1_subset_1(sK29,u1_struct_0(sK27)) ) ),
    introduced(choice_axiom,[])).

fof(f2081,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2080])).

fof(f2080,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2078])).

fof(f2078,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2077])).

fof(f2077,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

fof(f2444,plain,(
    ~ r3_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28)) ),
    inference(cnf_transformation,[],[f2303])).

fof(f2793,plain,(
    m1_subset_1(k7_lattices(sK27,sK28),u1_struct_0(sK27)) ),
    inference(unit_resulting_resolution,[],[f2437,f2440,f2441,f2445])).

fof(f2441,plain,(
    m1_subset_1(sK28,u1_struct_0(sK27)) ),
    inference(cnf_transformation,[],[f2303])).

fof(f2440,plain,(
    l3_lattices(sK27) ),
    inference(cnf_transformation,[],[f2303])).

fof(f2780,plain,(
    v9_lattices(sK27) ),
    inference(unit_resulting_resolution,[],[f2711,f2606])).

fof(f2606,plain,(
    ! [X0] :
      ( ~ sP19(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2401])).

fof(f2401,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP19(X0) ) ),
    inference(nnf_transformation,[],[f2287])).

fof(f2287,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP19(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP19])])).

fof(f2711,plain,(
    sP19(sK27) ),
    inference(global_subsumption,[],[f2440,f2437,f2707])).

fof(f2707,plain,
    ( sP19(sK27)
    | v2_struct_0(sK27)
    | ~ l3_lattices(sK27) ),
    inference(resolution,[],[f2438,f2607])).

fof(f2607,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | sP19(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2288])).

fof(f2288,plain,(
    ! [X0] :
      ( sP19(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f2204,f2287])).

fof(f2204,plain,(
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
    inference(flattening,[],[f2203])).

fof(f2203,plain,(
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

fof(f2438,plain,(
    v10_lattices(sK27) ),
    inference(cnf_transformation,[],[f2303])).

fof(f2779,plain,(
    v8_lattices(sK27) ),
    inference(unit_resulting_resolution,[],[f2711,f2605])).

fof(f2605,plain,(
    ! [X0] :
      ( ~ sP19(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2401])).

fof(f2777,plain,(
    v6_lattices(sK27) ),
    inference(unit_resulting_resolution,[],[f2711,f2603])).

fof(f2603,plain,(
    ! [X0] :
      ( ~ sP19(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2401])).

fof(f2437,plain,(
    ~ v2_struct_0(sK27) ),
    inference(cnf_transformation,[],[f2303])).

fof(f12186,plain,(
    r1_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28)) ),
    inference(backward_demodulation,[],[f11776,f12185])).

fof(f12185,plain,(
    k7_lattices(sK27,sK28) = k1_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28)) ),
    inference(forward_demodulation,[],[f11448,f3840])).

fof(f3840,plain,(
    k7_lattices(sK27,sK28) = k3_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28)) ),
    inference(backward_demodulation,[],[f3354,f3817])).

fof(f3817,plain,(
    sK28 = k4_lattices(sK27,sK28,sK29) ),
    inference(backward_demodulation,[],[f3027,f3805])).

fof(f3805,plain,(
    sK28 = k2_lattices(sK27,sK28,sK29) ),
    inference(unit_resulting_resolution,[],[f2437,f2779,f2780,f2440,f2441,f2442,f3754,f2521])).

fof(f2521,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2353])).

fof(f2353,plain,(
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
    inference(nnf_transformation,[],[f2152])).

fof(f2152,plain,(
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
    inference(flattening,[],[f2151])).

fof(f2151,plain,(
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
    inference(ennf_transformation,[],[f2055])).

fof(f2055,axiom,(
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

fof(f3754,plain,(
    r1_lattices(sK27,sK28,sK29) ),
    inference(unit_resulting_resolution,[],[f2437,f2777,f2779,f2780,f2440,f2441,f2442,f2443,f2453])).

fof(f2453,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2305])).

fof(f2443,plain,(
    r3_lattices(sK27,sK28,sK29) ),
    inference(cnf_transformation,[],[f2303])).

fof(f3027,plain,(
    k4_lattices(sK27,sK28,sK29) = k2_lattices(sK27,sK28,sK29) ),
    inference(unit_resulting_resolution,[],[f2437,f2777,f2738,f2441,f2442,f2485])).

fof(f2485,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2126])).

fof(f2126,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2125])).

fof(f2125,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2049])).

fof(f2049,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f2738,plain,(
    l1_lattices(sK27) ),
    inference(unit_resulting_resolution,[],[f2440,f2591])).

fof(f2591,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2192])).

fof(f2192,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2041])).

fof(f2041,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f3354,plain,(
    k3_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28)) = k7_lattices(sK27,k4_lattices(sK27,sK28,sK29)) ),
    inference(forward_demodulation,[],[f3003,f3021])).

fof(f3021,plain,(
    k4_lattices(sK27,sK29,sK28) = k4_lattices(sK27,sK28,sK29) ),
    inference(unit_resulting_resolution,[],[f2437,f2777,f2738,f2441,f2442,f2484])).

fof(f2484,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2124])).

fof(f2124,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2123])).

fof(f2123,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2017])).

fof(f2017,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f3003,plain,(
    k7_lattices(sK27,k4_lattices(sK27,sK29,sK28)) = k3_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28)) ),
    inference(unit_resulting_resolution,[],[f2437,f2438,f2439,f2440,f2441,f2442,f2448])).

fof(f2448,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2087])).

fof(f2087,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2086])).

fof(f2086,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2074])).

fof(f2074,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattices)).

fof(f2439,plain,(
    v17_lattices(sK27) ),
    inference(cnf_transformation,[],[f2303])).

fof(f11448,plain,(
    k3_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28)) = k1_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28)) ),
    inference(unit_resulting_resolution,[],[f2437,f2775,f2739,f2793,f3002,f2598])).

fof(f2598,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2200])).

fof(f2200,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2199])).

fof(f2199,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2047])).

fof(f2047,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f2739,plain,(
    l2_lattices(sK27) ),
    inference(unit_resulting_resolution,[],[f2440,f2592])).

fof(f2592,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2192])).

fof(f2775,plain,(
    v4_lattices(sK27) ),
    inference(unit_resulting_resolution,[],[f2711,f2601])).

fof(f2601,plain,(
    ! [X0] :
      ( ~ sP19(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2401])).

fof(f11776,plain,(
    r1_lattices(sK27,k7_lattices(sK27,sK29),k1_lattices(sK27,k7_lattices(sK27,sK29),k7_lattices(sK27,sK28))) ),
    inference(unit_resulting_resolution,[],[f2437,f2776,f2777,f2779,f2780,f2440,f2793,f3002,f2667])).

fof(f2667,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2244])).

fof(f2244,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2243])).

fof(f2243,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2056])).

fof(f2056,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_lattices)).

fof(f2776,plain,(
    v5_lattices(sK27) ),
    inference(unit_resulting_resolution,[],[f2711,f2602])).

fof(f2602,plain,(
    ! [X0] :
      ( ~ sP19(X0)
      | v5_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2401])).
%------------------------------------------------------------------------------
