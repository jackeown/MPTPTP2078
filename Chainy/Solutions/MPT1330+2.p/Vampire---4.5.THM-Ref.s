%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1330+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 196 expanded)
%              Number of leaves         :   25 (  87 expanded)
%              Depth                    :    9
%              Number of atoms          :  302 ( 902 expanded)
%              Number of equality atoms :   98 ( 346 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2610,f2617,f2621,f2625,f2629,f2633,f2637,f2672,f2676,f2689,f2715,f2850,f2878,f2883,f2955,f3078,f3231])).

fof(f3231,plain,
    ( ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_18
    | spl11_21 ),
    inference(avatar_contradiction_clause,[],[f3226])).

fof(f3226,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_6
    | spl11_18
    | spl11_21 ),
    inference(unit_resulting_resolution,[],[f2628,f2692,f2624,f2620,f2714,f2532])).

fof(f2532,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2429])).

fof(f2429,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f2428])).

fof(f2428,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1676])).

fof(f1676,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f2714,plain,
    ( u1_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | spl11_21 ),
    inference(avatar_component_clause,[],[f2713])).

fof(f2713,plain,
    ( spl11_21
  <=> u1_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f2620,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f2619])).

fof(f2619,plain,
    ( spl11_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f2624,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f2623])).

fof(f2623,plain,
    ( spl11_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f2692,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | spl11_18 ),
    inference(avatar_component_clause,[],[f2691])).

fof(f2691,plain,
    ( spl11_18
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f2628,plain,
    ( v1_funct_1(sK2)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f2627])).

fof(f2627,plain,
    ( spl11_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f3078,plain,
    ( ~ spl11_6
    | spl11_41
    | ~ spl11_42 ),
    inference(avatar_contradiction_clause,[],[f3076])).

fof(f3076,plain,
    ( $false
    | ~ spl11_6
    | spl11_41
    | ~ spl11_42 ),
    inference(unit_resulting_resolution,[],[f2877,f3067,f2565])).

fof(f2565,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2453])).

fof(f2453,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f3067,plain,
    ( ! [X2,X3] : r1_tarski(k8_relset_1(k1_xboole_0,X2,sK2,X3),k1_xboole_0)
    | ~ spl11_6
    | ~ spl11_42 ),
    inference(subsumption_resolution,[],[f3065,f2882])).

fof(f2882,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_42 ),
    inference(avatar_component_clause,[],[f2881])).

fof(f2881,plain,
    ( spl11_42
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f3065,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | r1_tarski(k8_relset_1(k1_xboole_0,X2,sK2,X3),k1_xboole_0) )
    | ~ spl11_6 ),
    inference(superposition,[],[f3003,f2603])).

fof(f2603,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f2555])).

fof(f2555,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2494])).

fof(f2494,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f2493])).

fof(f2493,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f3003,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | r1_tarski(k8_relset_1(X8,X9,sK2,X10),X8) )
    | ~ spl11_6 ),
    inference(resolution,[],[f2516,f2628])).

fof(f2516,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(cnf_transformation,[],[f2413])).

fof(f2413,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f2412])).

fof(f2412,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1675])).

fof(f1675,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_2)).

fof(f2877,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | spl11_41 ),
    inference(avatar_component_clause,[],[f2876])).

fof(f2876,plain,
    ( spl11_41
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f2955,plain,
    ( spl11_2
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f2943,f2691,f2670,f2612])).

fof(f2612,plain,
    ( spl11_2
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f2670,plain,
    ( spl11_14
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f2943,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl11_14
    | ~ spl11_18 ),
    inference(backward_demodulation,[],[f2671,f2828])).

fof(f2828,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f2691])).

fof(f2671,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f2670])).

fof(f2883,plain,
    ( spl11_42
    | ~ spl11_4
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f2879,f2786,f2619,f2881])).

fof(f2786,plain,
    ( spl11_27
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f2879,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl11_4
    | ~ spl11_27 ),
    inference(forward_demodulation,[],[f2868,f2603])).

fof(f2868,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl11_4
    | ~ spl11_27 ),
    inference(backward_demodulation,[],[f2620,f2787])).

fof(f2787,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f2786])).

fof(f2878,plain,
    ( ~ spl11_41
    | spl11_21
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f2867,f2786,f2713,f2876])).

fof(f2867,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | spl11_21
    | ~ spl11_27 ),
    inference(backward_demodulation,[],[f2714,f2787])).

fof(f2850,plain,
    ( spl11_27
    | ~ spl11_3
    | ~ spl11_15 ),
    inference(avatar_split_clause,[],[f2846,f2674,f2615,f2786])).

fof(f2615,plain,
    ( spl11_3
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f2674,plain,
    ( spl11_15
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f2846,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl11_3
    | ~ spl11_15 ),
    inference(backward_demodulation,[],[f2675,f2616])).

fof(f2616,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f2615])).

fof(f2675,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f2674])).

fof(f2715,plain,
    ( ~ spl11_21
    | ~ spl11_15
    | spl11_17 ),
    inference(avatar_split_clause,[],[f2709,f2687,f2674,f2713])).

fof(f2687,plain,
    ( spl11_17
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f2709,plain,
    ( u1_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | ~ spl11_15
    | spl11_17 ),
    inference(backward_demodulation,[],[f2688,f2675])).

fof(f2688,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | spl11_17 ),
    inference(avatar_component_clause,[],[f2687])).

fof(f2689,plain,
    ( ~ spl11_17
    | spl11_1
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f2682,f2670,f2608,f2687])).

fof(f2608,plain,
    ( spl11_1
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f2682,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(sK1))
    | spl11_1
    | ~ spl11_14 ),
    inference(backward_demodulation,[],[f2609,f2671])).

fof(f2609,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f2608])).

fof(f2676,plain,
    ( spl11_15
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f2667,f2635,f2674])).

fof(f2635,plain,
    ( spl11_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f2667,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl11_8 ),
    inference(resolution,[],[f2547,f2636])).

fof(f2636,plain,
    ( l1_struct_0(sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f2635])).

fof(f2547,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2440])).

fof(f2440,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f2672,plain,
    ( spl11_14
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f2666,f2631,f2670])).

fof(f2631,plain,
    ( spl11_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f2666,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl11_7 ),
    inference(resolution,[],[f2547,f2632])).

fof(f2632,plain,
    ( l1_struct_0(sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f2631])).

fof(f2637,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f2507,f2635])).

fof(f2507,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2481])).

fof(f2481,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2409,f2480,f2479,f2478])).

fof(f2478,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2479,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2480,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2409,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f2408])).

fof(f2408,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2395])).

fof(f2395,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2394])).

fof(f2394,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f2633,plain,(
    spl11_7 ),
    inference(avatar_split_clause,[],[f2508,f2631])).

fof(f2508,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f2481])).

fof(f2629,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f2509,f2627])).

fof(f2509,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f2481])).

fof(f2625,plain,(
    spl11_5 ),
    inference(avatar_split_clause,[],[f2510,f2623])).

fof(f2510,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f2481])).

fof(f2621,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f2511,f2619])).

fof(f2511,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f2481])).

fof(f2617,plain,
    ( ~ spl11_2
    | spl11_3 ),
    inference(avatar_split_clause,[],[f2512,f2615,f2612])).

fof(f2512,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f2481])).

fof(f2610,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f2513,f2608])).

fof(f2513,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f2481])).
%------------------------------------------------------------------------------
