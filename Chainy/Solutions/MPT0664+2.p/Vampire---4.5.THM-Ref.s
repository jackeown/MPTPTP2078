%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0664+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:43 EST 2020

% Result     : Theorem 2.92s
% Output     : Refutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 602 expanded)
%              Number of leaves         :   36 ( 184 expanded)
%              Depth                    :   11
%              Number of atoms          :  494 (2133 expanded)
%              Number of equality atoms :   79 ( 431 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2673,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2500,f2504,f2508,f2512,f2519,f2520,f2524,f2545,f2550,f2555,f2568,f2569,f2572,f2578,f2590,f2609,f2611,f2613,f2615,f2617,f2619,f2628,f2630,f2632,f2634,f2641,f2650,f2652,f2663,f2665,f2667,f2670,f2672])).

fof(f2672,plain,
    ( spl101_13
    | ~ spl101_18 ),
    inference(avatar_contradiction_clause,[],[f2671])).

fof(f2671,plain,
    ( $false
    | spl101_13
    | ~ spl101_18 ),
    inference(global_subsumption,[],[f1672,f1670,f2649,f2653])).

fof(f2653,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | spl101_13 ),
    inference(resolution,[],[f2571,f1677])).

fof(f1677,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1401])).

fof(f1401,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1400])).

fof(f1400,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f981])).

fof(f981,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f875])).

fof(f875,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f2571,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl101_13 ),
    inference(avatar_component_clause,[],[f2563])).

fof(f2563,plain,
    ( spl101_13
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_13])])).

fof(f2649,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl101_18 ),
    inference(avatar_component_clause,[],[f2648])).

fof(f2648,plain,
    ( spl101_18
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_18])])).

fof(f1670,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f1399])).

fof(f1399,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    & r2_hidden(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f978,f1398])).

fof(f1398,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
        & r2_hidden(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
      & r2_hidden(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f978,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f977])).

fof(f977,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k7_relat_1(X2,X1),X0)
      & r2_hidden(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f968])).

fof(f968,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,X1)
         => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f967])).

fof(f967,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(f1672,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f1399])).

fof(f2670,plain,
    ( spl101_13
    | ~ spl101_18 ),
    inference(avatar_contradiction_clause,[],[f2669])).

fof(f2669,plain,
    ( $false
    | spl101_13
    | ~ spl101_18 ),
    inference(global_subsumption,[],[f1672,f1670,f2649,f2653])).

fof(f2667,plain,
    ( spl101_13
    | ~ spl101_18 ),
    inference(avatar_contradiction_clause,[],[f2666])).

fof(f2666,plain,
    ( $false
    | spl101_13
    | ~ spl101_18 ),
    inference(global_subsumption,[],[f1672,f1670,f2649,f2653])).

fof(f2665,plain,
    ( spl101_13
    | ~ spl101_18 ),
    inference(avatar_contradiction_clause,[],[f2664])).

fof(f2664,plain,
    ( $false
    | spl101_13
    | ~ spl101_18 ),
    inference(global_subsumption,[],[f1672,f1670,f2649,f2653])).

fof(f2663,plain,
    ( spl101_13
    | ~ spl101_18 ),
    inference(avatar_contradiction_clause,[],[f2662])).

fof(f2662,plain,
    ( $false
    | spl101_13
    | ~ spl101_18 ),
    inference(global_subsumption,[],[f1672,f1670,f2649,f2653])).

fof(f2652,plain,
    ( spl101_18
    | spl101_14 ),
    inference(avatar_split_clause,[],[f2651,f2566,f2648])).

fof(f2566,plain,
    ( spl101_14
  <=> k1_xboole_0 = k1_funct_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_14])])).

fof(f2651,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | spl101_14 ),
    inference(global_subsumption,[],[f2646])).

fof(f2646,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | spl101_14 ),
    inference(global_subsumption,[],[f1671,f1670,f2645])).

fof(f2645,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl101_14 ),
    inference(trivial_inequality_removal,[],[f2642])).

fof(f2642,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl101_14 ),
    inference(superposition,[],[f2567,f2404])).

fof(f2404,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1765])).

fof(f1765,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1429])).

fof(f1429,plain,(
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
    inference(nnf_transformation,[],[f1063])).

fof(f1063,plain,(
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
    inference(flattening,[],[f1062])).

fof(f1062,plain,(
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
    inference(ennf_transformation,[],[f891])).

fof(f891,axiom,(
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

fof(f2567,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,sK0)
    | spl101_14 ),
    inference(avatar_component_clause,[],[f2566])).

fof(f1671,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1399])).

fof(f2650,plain,
    ( spl101_18
    | spl101_14 ),
    inference(avatar_split_clause,[],[f2646,f2566,f2648])).

fof(f2641,plain,(
    spl101_17 ),
    inference(avatar_contradiction_clause,[],[f2635])).

fof(f2635,plain,
    ( $false
    | spl101_17 ),
    inference(resolution,[],[f2589,f1892])).

fof(f1892,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f2589,plain,
    ( ~ r1_xboole_0(sK1,k1_xboole_0)
    | spl101_17 ),
    inference(avatar_component_clause,[],[f2588])).

fof(f2588,plain,
    ( spl101_17
  <=> r1_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_17])])).

fof(f2634,plain,(
    spl101_12 ),
    inference(avatar_contradiction_clause,[],[f2633])).

fof(f2633,plain,
    ( $false
    | spl101_12 ),
    inference(global_subsumption,[],[f1671,f1670,f2620])).

fof(f2620,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl101_12 ),
    inference(resolution,[],[f2561,f1688])).

fof(f1688,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f996])).

fof(f996,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f995])).

fof(f995,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f908])).

fof(f908,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f2561,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | spl101_12 ),
    inference(avatar_component_clause,[],[f2560])).

fof(f2560,plain,
    ( spl101_12
  <=> v1_funct_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_12])])).

fof(f2632,plain,(
    spl101_12 ),
    inference(avatar_contradiction_clause,[],[f2631])).

fof(f2631,plain,
    ( $false
    | spl101_12 ),
    inference(global_subsumption,[],[f1671,f1670,f2620])).

fof(f2630,plain,(
    spl101_12 ),
    inference(avatar_contradiction_clause,[],[f2629])).

fof(f2629,plain,
    ( $false
    | spl101_12 ),
    inference(global_subsumption,[],[f1671,f1670,f2620])).

fof(f2628,plain,(
    spl101_12 ),
    inference(avatar_contradiction_clause,[],[f2627])).

fof(f2627,plain,
    ( $false
    | spl101_12 ),
    inference(global_subsumption,[],[f1671,f1670,f2620])).

fof(f2619,plain,(
    spl101_11 ),
    inference(avatar_contradiction_clause,[],[f2618])).

fof(f2618,plain,
    ( $false
    | spl101_11 ),
    inference(global_subsumption,[],[f1670,f2597])).

fof(f2597,plain,
    ( ~ v1_relat_1(sK2)
    | spl101_11 ),
    inference(resolution,[],[f2558,f1708])).

fof(f1708,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1020])).

fof(f1020,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f669])).

fof(f669,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f2558,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl101_11 ),
    inference(avatar_component_clause,[],[f2557])).

fof(f2557,plain,
    ( spl101_11
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_11])])).

fof(f2617,plain,(
    spl101_11 ),
    inference(avatar_contradiction_clause,[],[f2616])).

fof(f2616,plain,
    ( $false
    | spl101_11 ),
    inference(global_subsumption,[],[f1670,f2597])).

fof(f2615,plain,(
    spl101_11 ),
    inference(avatar_contradiction_clause,[],[f2614])).

fof(f2614,plain,
    ( $false
    | spl101_11 ),
    inference(global_subsumption,[],[f1670,f2597])).

fof(f2613,plain,(
    spl101_11 ),
    inference(avatar_contradiction_clause,[],[f2612])).

fof(f2612,plain,
    ( $false
    | spl101_11 ),
    inference(global_subsumption,[],[f1670,f2597])).

fof(f2611,plain,(
    spl101_11 ),
    inference(avatar_contradiction_clause,[],[f2610])).

fof(f2610,plain,
    ( $false
    | spl101_11 ),
    inference(global_subsumption,[],[f1670,f2597])).

fof(f2609,plain,(
    spl101_11 ),
    inference(avatar_contradiction_clause,[],[f2608])).

fof(f2608,plain,
    ( $false
    | spl101_11 ),
    inference(global_subsumption,[],[f1670,f2597])).

fof(f2590,plain,
    ( ~ spl101_16
    | ~ spl101_17
    | spl101_8 ),
    inference(avatar_split_clause,[],[f2583,f2543,f2588,f2585])).

fof(f2585,plain,
    ( spl101_16
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_16])])).

fof(f2543,plain,
    ( spl101_8
  <=> r1_xboole_0(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_8])])).

fof(f2583,plain,
    ( ~ r1_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | spl101_8 ),
    inference(global_subsumption,[],[f1670,f2582])).

fof(f2582,plain,
    ( ~ r1_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl101_8 ),
    inference(superposition,[],[f2544,f2016])).

fof(f2016,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1507])).

fof(f1507,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1240])).

fof(f1240,plain,(
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

fof(f2544,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(sK2))
    | spl101_8 ),
    inference(avatar_component_clause,[],[f2543])).

fof(f2578,plain,
    ( ~ spl101_15
    | spl101_1 ),
    inference(avatar_split_clause,[],[f2574,f2498,f2576])).

fof(f2576,plain,
    ( spl101_15
  <=> r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_15])])).

fof(f2498,plain,
    ( spl101_1
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_1])])).

fof(f2574,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))
    | spl101_1 ),
    inference(global_subsumption,[],[f1671,f1670,f2573])).

fof(f2573,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl101_1 ),
    inference(forward_demodulation,[],[f2534,f1949])).

fof(f1949,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2534,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl101_1 ),
    inference(trivial_inequality_removal,[],[f2533])).

fof(f2533,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl101_1 ),
    inference(superposition,[],[f2499,f1725])).

fof(f1725,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1037])).

fof(f1037,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1036])).

fof(f1036,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f966])).

fof(f966,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

fof(f2499,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0)
    | spl101_1 ),
    inference(avatar_component_clause,[],[f2498])).

fof(f2572,plain,
    ( ~ spl101_13
    | spl101_1 ),
    inference(avatar_split_clause,[],[f2570,f2498,f2563])).

fof(f2570,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl101_1 ),
    inference(global_subsumption,[],[f1671,f1670,f2535])).

fof(f2535,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl101_1 ),
    inference(trivial_inequality_removal,[],[f2532])).

fof(f2532,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl101_1 ),
    inference(superposition,[],[f2499,f1726])).

fof(f1726,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1039])).

fof(f1039,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1038])).

fof(f1038,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f965])).

fof(f965,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

fof(f2569,plain,
    ( ~ spl101_11
    | ~ spl101_12
    | spl101_13
    | ~ spl101_14
    | spl101_1 ),
    inference(avatar_split_clause,[],[f2531,f2498,f2566,f2563,f2560,f2557])).

fof(f2531,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,sK0)
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl101_1 ),
    inference(superposition,[],[f2499,f2403])).

fof(f2403,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1766])).

fof(f1766,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1429])).

fof(f2568,plain,
    ( ~ spl101_11
    | ~ spl101_12
    | spl101_13
    | ~ spl101_14
    | spl101_1 ),
    inference(avatar_split_clause,[],[f2530,f2498,f2566,f2563,f2560,f2557])).

fof(f2530,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,sK0)
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_funct_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl101_1 ),
    inference(superposition,[],[f2499,f2404])).

fof(f2555,plain,
    ( ~ spl101_10
    | ~ spl101_7
    | spl101_1 ),
    inference(avatar_split_clause,[],[f2551,f2498,f2540,f2553])).

fof(f2553,plain,
    ( spl101_10
  <=> r1_xboole_0(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_10])])).

fof(f2540,plain,
    ( spl101_7
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_7])])).

fof(f2551,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k1_xboole_0,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | spl101_1 ),
    inference(global_subsumption,[],[f1670,f2529])).

fof(f2529,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k1_xboole_0,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl101_1 ),
    inference(superposition,[],[f2499,f1698])).

fof(f1698,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1402])).

fof(f1402,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1008])).

fof(f1008,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f884])).

fof(f884,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f2550,plain,
    ( ~ spl101_9
    | spl101_1 ),
    inference(avatar_split_clause,[],[f2546,f2498,f2548])).

fof(f2548,plain,
    ( spl101_9
  <=> r1_tarski(k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_9])])).

fof(f2546,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | spl101_1 ),
    inference(global_subsumption,[],[f1670,f2536])).

fof(f2536,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl101_1 ),
    inference(trivial_inequality_removal,[],[f2528])).

fof(f2528,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl101_1 ),
    inference(superposition,[],[f2499,f1699])).

fof(f1699,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1010])).

fof(f1010,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1009])).

fof(f1009,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f886])).

fof(f886,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f2545,plain,
    ( ~ spl101_7
    | ~ spl101_8
    | spl101_1 ),
    inference(avatar_split_clause,[],[f2538,f2498,f2543,f2540])).

fof(f2538,plain,
    ( ~ r1_xboole_0(sK1,k1_relat_1(sK2))
    | k1_funct_1(sK2,sK0) != k1_funct_1(k1_xboole_0,sK0)
    | spl101_1 ),
    inference(global_subsumption,[],[f1670,f2527])).

fof(f2527,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k1_xboole_0,sK0)
    | ~ r1_xboole_0(sK1,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl101_1 ),
    inference(superposition,[],[f2499,f1709])).

fof(f1709,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1021])).

fof(f1021,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f789])).

fof(f789,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f2524,plain,
    ( ~ spl101_6
    | ~ spl101_2 ),
    inference(avatar_split_clause,[],[f2515,f2502,f2522])).

fof(f2522,plain,
    ( spl101_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_6])])).

fof(f2502,plain,
    ( spl101_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_2])])).

fof(f2515,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl101_2 ),
    inference(resolution,[],[f2503,f1788])).

fof(f1788,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1073])).

fof(f1073,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f2503,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl101_2 ),
    inference(avatar_component_clause,[],[f2502])).

fof(f2520,plain,
    ( ~ spl101_5
    | ~ spl101_2 ),
    inference(avatar_split_clause,[],[f2514,f2502,f2517])).

fof(f2517,plain,
    ( spl101_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_5])])).

fof(f2514,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl101_2 ),
    inference(resolution,[],[f2503,f1960])).

fof(f1960,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1183])).

fof(f1183,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f2519,plain,
    ( ~ spl101_5
    | ~ spl101_2 ),
    inference(avatar_split_clause,[],[f2513,f2502,f2517])).

fof(f2513,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl101_2 ),
    inference(resolution,[],[f2503,f1977])).

fof(f1977,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1500])).

fof(f1500,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK38(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK38])],[f1498,f1499])).

fof(f1499,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK38(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1498,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1497])).

fof(f1497,plain,(
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

fof(f2512,plain,(
    spl101_4 ),
    inference(avatar_split_clause,[],[f1670,f2510])).

fof(f2510,plain,
    ( spl101_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_4])])).

fof(f2508,plain,(
    spl101_3 ),
    inference(avatar_split_clause,[],[f1671,f2506])).

fof(f2506,plain,
    ( spl101_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl101_3])])).

fof(f2504,plain,(
    spl101_2 ),
    inference(avatar_split_clause,[],[f1672,f2502])).

fof(f2500,plain,(
    ~ spl101_1 ),
    inference(avatar_split_clause,[],[f1673,f2498])).

fof(f1673,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f1399])).
%------------------------------------------------------------------------------
