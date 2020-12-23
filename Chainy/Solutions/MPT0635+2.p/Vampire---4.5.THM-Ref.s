%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0635+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:41 EST 2020

% Result     : Theorem 2.98s
% Output     : Refutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  234 ( 563 expanded)
%              Number of leaves         :   57 ( 210 expanded)
%              Depth                    :   10
%              Number of atoms          :  707 (1866 expanded)
%              Number of equality atoms :   97 ( 318 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2720,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2491,f2496,f2500,f2504,f2518,f2522,f2526,f2530,f2531,f2535,f2544,f2546,f2548,f2560,f2565,f2578,f2579,f2591,f2593,f2600,f2601,f2605,f2608,f2612,f2613,f2621,f2629,f2630,f2634,f2641,f2657,f2662,f2666,f2668,f2672,f2677,f2683,f2688,f2715,f2717])).

fof(f2717,plain,
    ( ~ spl100_6
    | spl100_19 ),
    inference(avatar_contradiction_clause,[],[f2716])).

fof(f2716,plain,
    ( $false
    | ~ spl100_6
    | spl100_19 ),
    inference(global_subsumption,[],[f2521,f2713])).

fof(f2713,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl100_19 ),
    inference(trivial_inequality_removal,[],[f2706])).

fof(f2706,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(sK0,sK1)
    | spl100_19 ),
    inference(superposition,[],[f2587,f1722])).

fof(f1722,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1005])).

fof(f1005,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f923])).

fof(f923,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

fof(f2587,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | spl100_19 ),
    inference(avatar_component_clause,[],[f2586])).

fof(f2586,plain,
    ( spl100_19
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_19])])).

fof(f2521,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl100_6 ),
    inference(avatar_component_clause,[],[f2520])).

fof(f2520,plain,
    ( spl100_6
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_6])])).

fof(f2715,plain,
    ( ~ spl100_6
    | spl100_19 ),
    inference(avatar_contradiction_clause,[],[f2714])).

fof(f2714,plain,
    ( $false
    | ~ spl100_6
    | spl100_19 ),
    inference(global_subsumption,[],[f2521,f2713])).

fof(f2688,plain,
    ( ~ spl100_31
    | spl100_15 ),
    inference(avatar_split_clause,[],[f2684,f2570,f2686])).

fof(f2686,plain,
    ( spl100_31
  <=> v1_funct_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_31])])).

fof(f2570,plain,
    ( spl100_15
  <=> v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_15])])).

fof(f2684,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | spl100_15 ),
    inference(global_subsumption,[],[f1644,f2680])).

fof(f2680,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl100_15 ),
    inference(superposition,[],[f2571,f1692])).

fof(f1692,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f984])).

fof(f984,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f883])).

fof(f883,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f2571,plain,
    ( ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | spl100_15 ),
    inference(avatar_component_clause,[],[f2570])).

fof(f1644,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1374])).

fof(f1374,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f936,f1373])).

fof(f1373,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f936,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f935])).

fof(f935,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f926])).

fof(f926,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f925])).

fof(f925,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

fof(f2683,plain,
    ( ~ spl100_20
    | ~ spl100_18
    | spl100_15 ),
    inference(avatar_split_clause,[],[f2682,f2570,f2583,f2589])).

fof(f2589,plain,
    ( spl100_20
  <=> v1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_20])])).

fof(f2583,plain,
    ( spl100_18
  <=> v1_funct_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_18])])).

fof(f2682,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl100_15 ),
    inference(global_subsumption,[],[f1645,f1644,f2678])).

fof(f2678,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl100_15 ),
    inference(resolution,[],[f2571,f1818])).

fof(f1818,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1052])).

fof(f1052,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1051])).

fof(f1051,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f898])).

fof(f898,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f1645,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1374])).

fof(f2677,plain,
    ( ~ spl100_30
    | spl100_14 ),
    inference(avatar_split_clause,[],[f2673,f2567,f2675])).

fof(f2675,plain,
    ( spl100_30
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_30])])).

fof(f2567,plain,
    ( spl100_14
  <=> v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_14])])).

fof(f2673,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl100_14 ),
    inference(global_subsumption,[],[f1644,f2653])).

fof(f2653,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl100_14 ),
    inference(superposition,[],[f2568,f1692])).

fof(f2568,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | spl100_14 ),
    inference(avatar_component_clause,[],[f2567])).

fof(f2672,plain,
    ( ~ spl100_29
    | spl100_14 ),
    inference(avatar_split_clause,[],[f2652,f2567,f2670])).

fof(f2670,plain,
    ( spl100_29
  <=> v1_xboole_0(k5_relat_1(k6_relat_1(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_29])])).

fof(f2652,plain,
    ( ~ v1_xboole_0(k5_relat_1(k6_relat_1(sK1),sK2))
    | spl100_14 ),
    inference(resolution,[],[f2568,f1860])).

fof(f1860,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1080])).

fof(f1080,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f2668,plain,
    ( ~ spl100_20
    | spl100_14 ),
    inference(avatar_split_clause,[],[f2667,f2567,f2589])).

fof(f2667,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl100_14 ),
    inference(global_subsumption,[],[f1644,f2651])).

fof(f2651,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl100_14 ),
    inference(resolution,[],[f2568,f1648])).

fof(f1648,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f938])).

fof(f938,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f937])).

fof(f937,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f667])).

fof(f667,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f2666,plain,
    ( ~ spl100_28
    | ~ spl100_20
    | spl100_14 ),
    inference(avatar_split_clause,[],[f2650,f2567,f2589,f2664])).

fof(f2664,plain,
    ( spl100_28
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_28])])).

fof(f2650,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | ~ v1_xboole_0(sK2)
    | spl100_14 ),
    inference(resolution,[],[f2568,f1650])).

fof(f1650,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f940])).

fof(f940,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f939])).

fof(f939,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f683])).

fof(f683,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_relat_1)).

fof(f2662,plain,
    ( ~ spl100_27
    | spl100_14 ),
    inference(avatar_split_clause,[],[f2658,f2567,f2660])).

fof(f2660,plain,
    ( spl100_27
  <=> v1_xboole_0(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_27])])).

fof(f2658,plain,
    ( ~ v1_xboole_0(k6_relat_1(sK1))
    | spl100_14 ),
    inference(global_subsumption,[],[f1644,f2649])).

fof(f2649,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(k6_relat_1(sK1))
    | spl100_14 ),
    inference(resolution,[],[f2568,f1652])).

fof(f1652,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f942])).

fof(f942,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f941])).

fof(f941,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f682])).

fof(f682,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_relat_1)).

fof(f2657,plain,
    ( ~ spl100_20
    | ~ spl100_18
    | spl100_14 ),
    inference(avatar_split_clause,[],[f2656,f2567,f2583,f2589])).

fof(f2656,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl100_14 ),
    inference(global_subsumption,[],[f1645,f1644,f2648])).

fof(f2648,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl100_14 ),
    inference(resolution,[],[f2568,f1817])).

fof(f1817,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1052])).

fof(f2641,plain,
    ( ~ spl100_26
    | spl100_10 ),
    inference(avatar_split_clause,[],[f2637,f2539,f2639])).

fof(f2639,plain,
    ( spl100_26
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_26])])).

fof(f2539,plain,
    ( spl100_10
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_10])])).

fof(f2637,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl100_10 ),
    inference(global_subsumption,[],[f1644,f2636])).

fof(f2636,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl100_10 ),
    inference(trivial_inequality_removal,[],[f2635])).

fof(f2635,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl100_10 ),
    inference(superposition,[],[f2540,f1917])).

fof(f1917,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1470])).

fof(f1470,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1141])).

fof(f1141,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f860])).

fof(f860,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f2540,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl100_10 ),
    inference(avatar_component_clause,[],[f2539])).

fof(f2634,plain,
    ( ~ spl100_25
    | ~ spl100_7 ),
    inference(avatar_split_clause,[],[f2624,f2524,f2632])).

fof(f2632,plain,
    ( spl100_25
  <=> r2_hidden(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_25])])).

fof(f2524,plain,
    ( spl100_7
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_7])])).

fof(f2624,plain,
    ( ~ r2_hidden(k1_relat_1(sK2),sK0)
    | ~ spl100_7 ),
    inference(resolution,[],[f2525,f1756])).

fof(f1756,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1019])).

fof(f1019,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f2525,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl100_7 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f2630,plain,
    ( ~ spl100_24
    | ~ spl100_7 ),
    inference(avatar_split_clause,[],[f2623,f2524,f2627])).

fof(f2627,plain,
    ( spl100_24
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_24])])).

fof(f2623,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl100_7 ),
    inference(resolution,[],[f2525,f1838])).

fof(f1838,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1062])).

fof(f1062,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f2629,plain,
    ( ~ spl100_24
    | ~ spl100_7 ),
    inference(avatar_split_clause,[],[f2622,f2524,f2627])).

fof(f2622,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl100_7 ),
    inference(resolution,[],[f2525,f1851])).

fof(f1851,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1457])).

fof(f1457,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK33(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33])],[f1455,f1456])).

fof(f1456,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK33(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1455,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1454])).

fof(f1454,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2621,plain,
    ( ~ spl100_23
    | spl100_5 ),
    inference(avatar_split_clause,[],[f2614,f2516,f2619])).

fof(f2619,plain,
    ( spl100_23
  <=> r1_xboole_0(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_23])])).

fof(f2516,plain,
    ( spl100_5
  <=> r1_xboole_0(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_5])])).

fof(f2614,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | spl100_5 ),
    inference(resolution,[],[f2517,f1990])).

fof(f1990,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1197])).

fof(f1197,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f2517,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(sK2))
    | spl100_5 ),
    inference(avatar_component_clause,[],[f2516])).

fof(f2613,plain,(
    spl100_20 ),
    inference(avatar_contradiction_clause,[],[f2609])).

fof(f2609,plain,
    ( $false
    | spl100_20 ),
    inference(resolution,[],[f2590,f1700])).

fof(f1700,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f2590,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | spl100_20 ),
    inference(avatar_component_clause,[],[f2589])).

fof(f2612,plain,(
    spl100_20 ),
    inference(avatar_contradiction_clause,[],[f2610])).

fof(f2610,plain,
    ( $false
    | spl100_20 ),
    inference(resolution,[],[f2590,f1698])).

fof(f1698,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f899])).

fof(f899,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f2608,plain,(
    spl100_18 ),
    inference(avatar_contradiction_clause,[],[f2606])).

fof(f2606,plain,
    ( $false
    | spl100_18 ),
    inference(resolution,[],[f2584,f1699])).

fof(f1699,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f899])).

fof(f2584,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | spl100_18 ),
    inference(avatar_component_clause,[],[f2583])).

fof(f2605,plain,
    ( ~ spl100_22
    | ~ spl100_6 ),
    inference(avatar_split_clause,[],[f2596,f2520,f2603])).

fof(f2603,plain,
    ( spl100_22
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_22])])).

fof(f2596,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl100_6 ),
    inference(resolution,[],[f2521,f1756])).

fof(f2601,plain,
    ( ~ spl100_21
    | ~ spl100_6 ),
    inference(avatar_split_clause,[],[f2595,f2520,f2598])).

fof(f2598,plain,
    ( spl100_21
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_21])])).

fof(f2595,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl100_6 ),
    inference(resolution,[],[f2521,f1838])).

fof(f2600,plain,
    ( ~ spl100_21
    | ~ spl100_6 ),
    inference(avatar_split_clause,[],[f2594,f2520,f2598])).

fof(f2594,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl100_6 ),
    inference(resolution,[],[f2521,f1851])).

fof(f2593,plain,
    ( ~ spl100_19
    | ~ spl100_20
    | ~ spl100_18
    | spl100_1
    | ~ spl100_6 ),
    inference(avatar_split_clause,[],[f2592,f2520,f2489,f2583,f2589,f2586])).

fof(f2489,plain,
    ( spl100_1
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_1])])).

fof(f2592,plain,
    ( ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | spl100_1
    | ~ spl100_6 ),
    inference(global_subsumption,[],[f2581])).

fof(f2581,plain,
    ( ~ v1_relat_1(k6_relat_1(sK1))
    | k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | spl100_1
    | ~ spl100_6 ),
    inference(global_subsumption,[],[f1645,f1644,f2521,f2580])).

fof(f2580,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl100_1 ),
    inference(forward_demodulation,[],[f2553,f1696])).

fof(f1696,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f2553,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1))
    | spl100_1 ),
    inference(superposition,[],[f2490,f1713])).

fof(f1713,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f996])).

fof(f996,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f995])).

fof(f995,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f918])).

fof(f918,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f2490,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    | spl100_1 ),
    inference(avatar_component_clause,[],[f2489])).

fof(f2591,plain,
    ( ~ spl100_18
    | ~ spl100_19
    | ~ spl100_20
    | spl100_1
    | ~ spl100_6 ),
    inference(avatar_split_clause,[],[f2581,f2520,f2489,f2589,f2586,f2583])).

fof(f2579,plain,
    ( ~ spl100_14
    | ~ spl100_15
    | spl100_16
    | ~ spl100_17
    | spl100_1 ),
    inference(avatar_split_clause,[],[f2552,f2489,f2576,f2573,f2570,f2567])).

fof(f2573,plain,
    ( spl100_16
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_16])])).

fof(f2576,plain,
    ( spl100_17
  <=> k1_xboole_0 = k1_funct_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_17])])).

fof(f2552,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,sK0)
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | spl100_1 ),
    inference(superposition,[],[f2490,f2396])).

fof(f2396,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1734])).

fof(f1734,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1403])).

fof(f1403,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1009])).

fof(f1009,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1008])).

fof(f1008,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f2578,plain,
    ( ~ spl100_14
    | ~ spl100_15
    | spl100_16
    | ~ spl100_17
    | spl100_1 ),
    inference(avatar_split_clause,[],[f2551,f2489,f2576,f2573,f2570,f2567])).

fof(f2551,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,sK0)
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2)))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK1),sK2))
    | spl100_1 ),
    inference(superposition,[],[f2490,f2397])).

fof(f2397,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1733])).

fof(f1733,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1403])).

fof(f2565,plain,
    ( ~ spl100_13
    | spl100_1 ),
    inference(avatar_split_clause,[],[f2561,f2489,f2563])).

fof(f2563,plain,
    ( spl100_13
  <=> r1_tarski(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_13])])).

fof(f2561,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | spl100_1 ),
    inference(global_subsumption,[],[f1644,f2555])).

fof(f2555,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl100_1 ),
    inference(trivial_inequality_removal,[],[f2550])).

fof(f2550,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl100_1 ),
    inference(superposition,[],[f2490,f1688])).

fof(f1688,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f980])).

fof(f980,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f979])).

fof(f979,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f869])).

fof(f869,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f2560,plain,
    ( ~ spl100_12
    | spl100_1 ),
    inference(avatar_split_clause,[],[f2556,f2489,f2558])).

fof(f2558,plain,
    ( spl100_12
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_12])])).

fof(f2556,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | spl100_1 ),
    inference(global_subsumption,[],[f1644,f2549])).

fof(f2549,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | ~ v1_relat_1(sK2)
    | spl100_1 ),
    inference(superposition,[],[f2490,f1692])).

fof(f2548,plain,
    ( spl100_6
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2547,f2494,f2520])).

fof(f2494,plain,
    ( spl100_2
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_2])])).

fof(f2547,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl100_2 ),
    inference(global_subsumption,[],[f2506])).

fof(f2506,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl100_2 ),
    inference(resolution,[],[f2495,f2405])).

fof(f2405,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f1759])).

fof(f1759,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f1430,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK20(X0,X1,X2),X1)
            | ~ r2_hidden(sK20(X0,X1,X2),X0)
            | ~ r2_hidden(sK20(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK20(X0,X1,X2),X1)
              & r2_hidden(sK20(X0,X1,X2),X0) )
            | r2_hidden(sK20(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f1428,f1429])).

fof(f1429,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK20(X0,X1,X2),X1)
          | ~ r2_hidden(sK20(X0,X1,X2),X0)
          | ~ r2_hidden(sK20(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK20(X0,X1,X2),X1)
            & r2_hidden(sK20(X0,X1,X2),X0) )
          | r2_hidden(sK20(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1428,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f1427])).

fof(f1427,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f1426])).

fof(f1426,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2495,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl100_2 ),
    inference(avatar_component_clause,[],[f2494])).

fof(f2546,plain,
    ( ~ spl100_5
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2545,f2494,f2516])).

fof(f2545,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(sK2))
    | ~ spl100_2 ),
    inference(global_subsumption,[],[f2505])).

fof(f2505,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(sK2))
    | ~ spl100_2 ),
    inference(resolution,[],[f2495,f1999])).

fof(f1999,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1485])).

fof(f1485,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK41(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK41])],[f1202,f1484])).

fof(f1484,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK41(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f1202,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f933])).

fof(f933,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f2544,plain,
    ( ~ spl100_10
    | spl100_11
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2537,f2494,f2542,f2539])).

fof(f2542,plain,
    ( spl100_11
  <=> r2_hidden(sK0,k3_xboole_0(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_11])])).

fof(f2537,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_xboole_0,sK1))
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl100_2 ),
    inference(global_subsumption,[],[f1644,f2536])).

fof(f2536,plain,
    ( r2_hidden(sK0,k3_xboole_0(k1_xboole_0,sK1))
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl100_2 ),
    inference(forward_demodulation,[],[f2511,f1790])).

fof(f1790,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2511,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK1,k1_xboole_0))
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl100_2 ),
    inference(superposition,[],[f2495,f1918])).

fof(f1918,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1470])).

fof(f2535,plain,
    ( ~ spl100_9
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2510,f2494,f2533])).

fof(f2533,plain,
    ( spl100_9
  <=> r2_hidden(k3_xboole_0(sK1,k1_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_9])])).

fof(f2510,plain,
    ( ~ r2_hidden(k3_xboole_0(sK1,k1_relat_1(sK2)),sK0)
    | ~ spl100_2 ),
    inference(resolution,[],[f2495,f1756])).

fof(f2531,plain,
    ( ~ spl100_8
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2509,f2494,f2528])).

fof(f2528,plain,
    ( spl100_8
  <=> v1_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_8])])).

fof(f2509,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl100_2 ),
    inference(resolution,[],[f2495,f1838])).

fof(f2530,plain,
    ( ~ spl100_8
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2508,f2494,f2528])).

fof(f2508,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ spl100_2 ),
    inference(resolution,[],[f2495,f1851])).

fof(f2526,plain,
    ( spl100_7
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2507,f2494,f2524])).

fof(f2507,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl100_2 ),
    inference(resolution,[],[f2495,f2404])).

fof(f2404,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f1760])).

fof(f1760,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1430])).

fof(f2522,plain,
    ( spl100_6
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2506,f2494,f2520])).

fof(f2518,plain,
    ( ~ spl100_5
    | ~ spl100_2 ),
    inference(avatar_split_clause,[],[f2505,f2494,f2516])).

fof(f2504,plain,(
    spl100_4 ),
    inference(avatar_split_clause,[],[f1644,f2502])).

fof(f2502,plain,
    ( spl100_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_4])])).

fof(f2500,plain,(
    spl100_3 ),
    inference(avatar_split_clause,[],[f1645,f2498])).

fof(f2498,plain,
    ( spl100_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl100_3])])).

fof(f2496,plain,(
    spl100_2 ),
    inference(avatar_split_clause,[],[f2492,f2494])).

fof(f2492,plain,(
    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f1646,f1790])).

fof(f1646,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f1374])).

fof(f2491,plain,(
    ~ spl100_1 ),
    inference(avatar_split_clause,[],[f1647,f2489])).

fof(f1647,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    inference(cnf_transformation,[],[f1374])).
%------------------------------------------------------------------------------
