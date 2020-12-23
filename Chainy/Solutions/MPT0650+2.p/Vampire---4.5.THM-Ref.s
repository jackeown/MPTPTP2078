%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0650+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:42 EST 2020

% Result     : Theorem 2.89s
% Output     : Refutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 660 expanded)
%              Number of leaves         :   38 ( 210 expanded)
%              Depth                    :   14
%              Number of atoms          :  702 (3348 expanded)
%              Number of equality atoms :  179 (1007 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2994,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2849,f2853,f2857,f2861,f2865,f2873,f2874,f2878,f2886,f2898,f2911,f2912,f2914,f2922,f2924,f2934,f2940,f2945,f2947,f2949,f2954,f2956,f2958,f2963,f2966,f2974,f2987,f2989,f2991,f2993])).

fof(f2993,plain,(
    spl118_14 ),
    inference(avatar_contradiction_clause,[],[f2992])).

fof(f2992,plain,
    ( $false
    | spl118_14 ),
    inference(global_subsumption,[],[f1827,f1826,f1825,f1824,f2980])).

fof(f2980,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_14 ),
    inference(superposition,[],[f2965,f1920])).

fof(f1920,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1024])).

fof(f1024,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1023])).

fof(f1023,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f947])).

fof(f947,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f2965,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | spl118_14 ),
    inference(avatar_component_clause,[],[f2906])).

fof(f2906,plain,
    ( spl118_14
  <=> r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_14])])).

fof(f1824,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1506])).

fof(f1506,plain,
    ( ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
      | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) )
    & r2_hidden(sK0,k2_relat_1(sK1))
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f960,f1505])).

fof(f1505,plain,
    ( ? [X0,X1] :
        ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
          | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
        & r2_hidden(X0,k2_relat_1(X1))
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
        | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) )
      & r2_hidden(sK0,k2_relat_1(sK1))
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f960,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f959])).

fof(f959,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f950])).

fof(f950,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f949])).

fof(f949,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f1825,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1506])).

fof(f1826,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1506])).

fof(f1827,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1506])).

fof(f2991,plain,(
    spl118_14 ),
    inference(avatar_contradiction_clause,[],[f2990])).

fof(f2990,plain,
    ( $false
    | spl118_14 ),
    inference(global_subsumption,[],[f1827,f1826,f1825,f1824,f2980])).

fof(f2989,plain,(
    spl118_14 ),
    inference(avatar_contradiction_clause,[],[f2988])).

fof(f2988,plain,
    ( $false
    | spl118_14 ),
    inference(global_subsumption,[],[f1827,f1826,f1825,f1824,f2980])).

fof(f2987,plain,
    ( ~ spl118_22
    | spl118_14 ),
    inference(avatar_split_clause,[],[f2983,f2906,f2985])).

fof(f2985,plain,
    ( spl118_22
  <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_22])])).

fof(f2983,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | spl118_14 ),
    inference(global_subsumption,[],[f1826,f1825,f1824,f2979])).

fof(f2979,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_14 ),
    inference(superposition,[],[f2965,f1922])).

fof(f1922,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1026])).

fof(f1026,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1025])).

fof(f1025,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f894])).

fof(f894,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f2974,plain,
    ( ~ spl118_21
    | spl118_10 ),
    inference(avatar_split_clause,[],[f2970,f2884,f2972])).

fof(f2972,plain,
    ( spl118_21
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_21])])).

fof(f2884,plain,
    ( spl118_10
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_10])])).

fof(f2970,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | spl118_10 ),
    inference(global_subsumption,[],[f1824,f2969])).

fof(f2969,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_10 ),
    inference(trivial_inequality_removal,[],[f2968])).

fof(f2968,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_10 ),
    inference(superposition,[],[f2885,f1941])).

fof(f1941,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1562])).

fof(f1562,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1043])).

fof(f1043,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f2885,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | spl118_10 ),
    inference(avatar_component_clause,[],[f2884])).

fof(f2966,plain,
    ( ~ spl118_14
    | ~ spl118_12
    | ~ spl118_13
    | ~ spl118_1
    | spl118_2 ),
    inference(avatar_split_clause,[],[f2964,f2847,f2844,f2903,f2900,f2906])).

fof(f2900,plain,
    ( spl118_12
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_12])])).

fof(f2903,plain,
    ( spl118_13
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_13])])).

fof(f2844,plain,
    ( spl118_1
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_1])])).

fof(f2847,plain,
    ( spl118_2
  <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_2])])).

fof(f2964,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | spl118_2 ),
    inference(global_subsumption,[],[f1825,f1824,f2928])).

fof(f2928,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl118_2 ),
    inference(superposition,[],[f2848,f1860])).

fof(f1860,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f997])).

fof(f997,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f996])).

fof(f996,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f927])).

fof(f927,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f2848,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | spl118_2 ),
    inference(avatar_component_clause,[],[f2847])).

fof(f2963,plain,
    ( ~ spl118_20
    | ~ spl118_13
    | ~ spl118_12
    | ~ spl118_1
    | spl118_2 ),
    inference(avatar_split_clause,[],[f2959,f2847,f2844,f2900,f2903,f2961])).

fof(f2961,plain,
    ( spl118_20
  <=> r2_hidden(sK0,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_20])])).

fof(f2959,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)))
    | spl118_2 ),
    inference(global_subsumption,[],[f1825,f1824,f2929])).

fof(f2929,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_2 ),
    inference(superposition,[],[f2848,f1859])).

fof(f1859,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f995])).

fof(f995,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f994])).

fof(f994,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f926])).

fof(f926,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f2958,plain,(
    spl118_13 ),
    inference(avatar_contradiction_clause,[],[f2957])).

fof(f2957,plain,
    ( $false
    | spl118_13 ),
    inference(global_subsumption,[],[f1825,f1824,f2950])).

fof(f2950,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_13 ),
    inference(resolution,[],[f2904,f1924])).

fof(f1924,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1028])).

fof(f1028,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1027])).

fof(f1027,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f896])).

fof(f896,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f2904,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl118_13 ),
    inference(avatar_component_clause,[],[f2903])).

fof(f2956,plain,(
    spl118_13 ),
    inference(avatar_contradiction_clause,[],[f2955])).

fof(f2955,plain,
    ( $false
    | spl118_13 ),
    inference(global_subsumption,[],[f1825,f1824,f2950])).

fof(f2954,plain,(
    spl118_13 ),
    inference(avatar_contradiction_clause,[],[f2953])).

fof(f2953,plain,
    ( $false
    | spl118_13 ),
    inference(global_subsumption,[],[f1825,f1824,f2950])).

fof(f2949,plain,(
    spl118_12 ),
    inference(avatar_contradiction_clause,[],[f2948])).

fof(f2948,plain,
    ( $false
    | spl118_12 ),
    inference(global_subsumption,[],[f1825,f1824,f2941])).

fof(f2941,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_12 ),
    inference(resolution,[],[f2901,f1923])).

fof(f1923,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1028])).

fof(f2901,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl118_12 ),
    inference(avatar_component_clause,[],[f2900])).

fof(f2947,plain,(
    spl118_12 ),
    inference(avatar_contradiction_clause,[],[f2946])).

fof(f2946,plain,
    ( $false
    | spl118_12 ),
    inference(global_subsumption,[],[f1825,f1824,f2941])).

fof(f2945,plain,(
    spl118_12 ),
    inference(avatar_contradiction_clause,[],[f2944])).

fof(f2944,plain,
    ( $false
    | spl118_12 ),
    inference(global_subsumption,[],[f1825,f1824,f2941])).

fof(f2940,plain,
    ( ~ spl118_19
    | spl118_7 ),
    inference(avatar_split_clause,[],[f2935,f2871,f2938])).

% (25318)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
fof(f2938,plain,
    ( spl118_19
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_19])])).

fof(f2871,plain,
    ( spl118_7
  <=> v1_xboole_0(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_7])])).

fof(f2935,plain,
    ( ~ v1_xboole_0(sK1)
    | spl118_7 ),
    inference(resolution,[],[f2872,f2352])).

fof(f2352,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1260])).

fof(f1260,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f681])).

fof(f681,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f2872,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK1))
    | spl118_7 ),
    inference(avatar_component_clause,[],[f2871])).

fof(f2934,plain,
    ( ~ spl118_18
    | spl118_2 ),
    inference(avatar_split_clause,[],[f2930,f2847,f2932])).

fof(f2932,plain,
    ( spl118_18
  <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_18])])).

fof(f2930,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl118_2 ),
    inference(global_subsumption,[],[f1826,f1825,f1824,f2925])).

fof(f2925,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_2 ),
    inference(superposition,[],[f2848,f1922])).

fof(f2924,plain,
    ( ~ spl118_16
    | spl118_17
    | spl118_1 ),
    inference(avatar_split_clause,[],[f2923,f2844,f2920,f2917])).

fof(f2917,plain,
    ( spl118_16
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_16])])).

fof(f2920,plain,
    ( spl118_17
  <=> r2_hidden(k1_funct_1(k2_funct_1(sK1),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_17])])).

fof(f2923,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK1),sK0),k1_relat_1(sK1))
    | k1_xboole_0 != sK0
    | spl118_1 ),
    inference(global_subsumption,[],[f2915])).

fof(f2915,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK1),sK0),k1_relat_1(sK1))
    | k1_xboole_0 != sK0
    | spl118_1 ),
    inference(global_subsumption,[],[f1825,f1824,f2891])).

fof(f2891,plain,
    ( k1_xboole_0 != sK0
    | r2_hidden(k1_funct_1(k2_funct_1(sK1),sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_1 ),
    inference(superposition,[],[f2845,f2730])).

fof(f2730,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1888])).

fof(f1888,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1530])).

fof(f1530,plain,(
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
    inference(nnf_transformation,[],[f1012])).

fof(f1012,plain,(
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
    inference(flattening,[],[f1011])).

fof(f1011,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f2845,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | spl118_1 ),
    inference(avatar_component_clause,[],[f2844])).

fof(f2922,plain,
    ( ~ spl118_16
    | spl118_17
    | spl118_1 ),
    inference(avatar_split_clause,[],[f2915,f2844,f2920,f2917])).

fof(f2914,plain,
    ( ~ spl118_13
    | ~ spl118_12
    | spl118_1 ),
    inference(avatar_split_clause,[],[f2913,f2844,f2900,f2903])).

fof(f2913,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl118_1 ),
    inference(global_subsumption,[],[f1827,f1826,f1825,f1824,f2893])).

fof(f2893,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_1 ),
    inference(trivial_inequality_removal,[],[f2890])).

fof(f2890,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_1 ),
    inference(superposition,[],[f2845,f2741])).

fof(f2741,plain,(
    ! [X4,X0] :
      ( k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),X4)) = X4
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2740])).

fof(f2740,plain,(
    ! [X4,X0,X1] :
      ( k1_funct_1(X0,k1_funct_1(X1,X4)) = X4
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1908])).

fof(f1908,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X0,X5) = X4
      | k1_funct_1(X1,X4) != X5
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1548])).

fof(f1548,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( sK16(X0,X1) != k1_funct_1(X1,sK15(X0,X1))
                  | ~ r2_hidden(sK15(X0,X1),k2_relat_1(X0)) )
                & sK15(X0,X1) = k1_funct_1(X0,sK16(X0,X1))
                & r2_hidden(sK16(X0,X1),k1_relat_1(X0)) )
              | ( ( sK15(X0,X1) != k1_funct_1(X0,sK16(X0,X1))
                  | ~ r2_hidden(sK16(X0,X1),k1_relat_1(X0)) )
                & sK16(X0,X1) = k1_funct_1(X1,sK15(X0,X1))
                & r2_hidden(sK15(X0,X1),k2_relat_1(X0)) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f1546,f1547])).

fof(f1547,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( sK16(X0,X1) != k1_funct_1(X1,sK15(X0,X1))
            | ~ r2_hidden(sK15(X0,X1),k2_relat_1(X0)) )
          & sK15(X0,X1) = k1_funct_1(X0,sK16(X0,X1))
          & r2_hidden(sK16(X0,X1),k1_relat_1(X0)) )
        | ( ( sK15(X0,X1) != k1_funct_1(X0,sK16(X0,X1))
            | ~ r2_hidden(sK16(X0,X1),k1_relat_1(X0)) )
          & sK16(X0,X1) = k1_funct_1(X1,sK15(X0,X1))
          & r2_hidden(sK15(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1546,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1545])).

fof(f1545,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1544])).

fof(f1544,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k2_relat_1(X0) != k1_relat_1(X1) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1022])).

fof(f1022,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1021])).

fof(f1021,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f946])).

fof(f946,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f2912,plain,
    ( ~ spl118_12
    | ~ spl118_13
    | spl118_14
    | ~ spl118_15
    | spl118_1 ),
    inference(avatar_split_clause,[],[f2889,f2844,f2909,f2906,f2903,f2900])).

fof(f2909,plain,
    ( spl118_15
  <=> sK0 = k1_funct_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_15])])).

fof(f2889,plain,
    ( sK0 != k1_funct_1(sK1,k1_xboole_0)
    | r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl118_1 ),
    inference(superposition,[],[f2845,f2729])).

fof(f2729,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_funct_1(X0,X1)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f1889])).

fof(f1889,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) = X2
      | k1_xboole_0 != X2
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1530])).

fof(f2911,plain,
    ( ~ spl118_12
    | ~ spl118_13
    | spl118_14
    | ~ spl118_15
    | spl118_1 ),
    inference(avatar_split_clause,[],[f2888,f2844,f2909,f2906,f2903,f2900])).

fof(f2888,plain,
    ( sK0 != k1_funct_1(sK1,k1_xboole_0)
    | r2_hidden(sK0,k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | spl118_1 ),
    inference(superposition,[],[f2845,f2730])).

fof(f2898,plain,
    ( ~ spl118_11
    | spl118_1 ),
    inference(avatar_split_clause,[],[f2894,f2844,f2896])).

fof(f2896,plain,
    ( spl118_11
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_11])])).

fof(f2894,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | spl118_1 ),
    inference(global_subsumption,[],[f1826,f1825,f1824,f2887])).

fof(f2887,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl118_1 ),
    inference(superposition,[],[f2845,f1922])).

fof(f2886,plain,
    ( spl118_9
    | ~ spl118_10
    | ~ spl118_3 ),
    inference(avatar_split_clause,[],[f2879,f2851,f2884,f2881])).

fof(f2881,plain,
    ( spl118_9
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_9])])).

fof(f2851,plain,
    ( spl118_3
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_3])])).

fof(f2879,plain,
    ( k1_xboole_0 != k1_relat_1(sK1)
    | r2_hidden(sK0,k1_xboole_0)
    | ~ spl118_3 ),
    inference(global_subsumption,[],[f1824,f2869])).

fof(f2869,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl118_3 ),
    inference(superposition,[],[f2852,f1940])).

fof(f1940,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1562])).

fof(f2852,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl118_3 ),
    inference(avatar_component_clause,[],[f2851])).

fof(f2878,plain,
    ( ~ spl118_8
    | ~ spl118_3 ),
    inference(avatar_split_clause,[],[f2868,f2851,f2876])).

fof(f2876,plain,
    ( spl118_8
  <=> r2_hidden(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_8])])).

fof(f2868,plain,
    ( ~ r2_hidden(k2_relat_1(sK1),sK0)
    | ~ spl118_3 ),
    inference(resolution,[],[f2852,f1932])).

fof(f1932,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1032])).

fof(f1032,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f2874,plain,
    ( ~ spl118_7
    | ~ spl118_3 ),
    inference(avatar_split_clause,[],[f2867,f2851,f2871])).

fof(f2867,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK1))
    | ~ spl118_3 ),
    inference(resolution,[],[f2852,f2329])).

fof(f2329,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1241])).

fof(f1241,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f2873,plain,
    ( ~ spl118_7
    | ~ spl118_3 ),
    inference(avatar_split_clause,[],[f2866,f2851,f2871])).

fof(f2866,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK1))
    | ~ spl118_3 ),
    inference(resolution,[],[f2852,f2346])).

fof(f2346,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1727])).

fof(f1727,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK96(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK96])],[f1725,f1726])).

fof(f1726,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK96(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1725,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1724])).

fof(f1724,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2865,plain,(
    spl118_6 ),
    inference(avatar_split_clause,[],[f1824,f2863])).

fof(f2863,plain,
    ( spl118_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_6])])).

fof(f2861,plain,(
    spl118_5 ),
    inference(avatar_split_clause,[],[f1825,f2859])).

fof(f2859,plain,
    ( spl118_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_5])])).

fof(f2857,plain,(
    spl118_4 ),
    inference(avatar_split_clause,[],[f1826,f2855])).

fof(f2855,plain,
    ( spl118_4
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_4])])).

fof(f2853,plain,(
    spl118_3 ),
    inference(avatar_split_clause,[],[f1827,f2851])).

fof(f2849,plain,
    ( ~ spl118_1
    | ~ spl118_2 ),
    inference(avatar_split_clause,[],[f1828,f2847,f2844])).

fof(f1828,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f1506])).
%------------------------------------------------------------------------------
