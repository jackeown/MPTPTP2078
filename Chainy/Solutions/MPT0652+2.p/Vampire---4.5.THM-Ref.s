%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0652+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:42 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  377 (1368 expanded)
%              Number of leaves         :   89 ( 474 expanded)
%              Depth                    :    9
%              Number of atoms          : 1278 (5626 expanded)
%              Number of equality atoms :  303 (1887 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2858,f2862,f2866,f2870,f2881,f2889,f2897,f2902,f2904,f2914,f2926,f2931,f2933,f2935,f2940,f2942,f2947,f2952,f2959,f2970,f2974,f2979,f2981,f2985,f2990,f3001,f3003,f3013,f3018,f3025,f3035,f3047,f3052,f3057,f3059,f3063,f3084,f3089,f3091,f3100,f3117,f3122,f3148,f3153,f3161,f3165,f3169,f3173,f3177,f3181,f3182,f3217,f3219,f3225,f3227,f3232,f3234,f3249,f3253,f3295,f3326,f3331,f3335,f3340,f3349,f3359,f3361,f3367,f3368,f3372])).

fof(f3372,plain,
    ( ~ spl117_27
    | spl117_17 ),
    inference(avatar_split_clause,[],[f3371,f2945,f3016])).

fof(f3016,plain,
    ( spl117_27
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_27])])).

fof(f2945,plain,
    ( spl117_17
  <=> r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_17])])).

fof(f3371,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl117_17 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3029])).

fof(f3029,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_17 ),
    inference(superposition,[],[f2946,f1874])).

fof(f1874,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1000])).

fof(f1000,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f999])).

fof(f999,plain,(
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

fof(f2946,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | spl117_17 ),
    inference(avatar_component_clause,[],[f2945])).

fof(f1830,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1512])).

fof(f1512,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f962,f1511])).

fof(f1511,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f962,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f961])).

fof(f961,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f952])).

fof(f952,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f951])).

fof(f951,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f1831,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1512])).

fof(f1832,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1512])).

fof(f3368,plain,(
    spl117_27 ),
    inference(avatar_contradiction_clause,[],[f3363])).

fof(f3363,plain,
    ( $false
    | spl117_27 ),
    inference(resolution,[],[f3017,f2748])).

fof(f2748,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1963])).

fof(f1963,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1549])).

fof(f1549,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1548])).

fof(f1548,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3017,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl117_27 ),
    inference(avatar_component_clause,[],[f3016])).

fof(f3367,plain,(
    spl117_27 ),
    inference(avatar_contradiction_clause,[],[f3364])).

fof(f3364,plain,
    ( $false
    | spl117_27 ),
    inference(resolution,[],[f3017,f2747])).

fof(f2747,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1964])).

fof(f1964,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1549])).

fof(f3361,plain,
    ( ~ spl117_36
    | spl117_24 ),
    inference(avatar_split_clause,[],[f3360,f2988,f3082])).

fof(f3082,plain,
    ( spl117_36
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_36])])).

fof(f2988,plain,
    ( spl117_24
  <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_24])])).

fof(f3360,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl117_24 ),
    inference(global_subsumption,[],[f1830,f3353])).

fof(f3353,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl117_24 ),
    inference(resolution,[],[f2989,f1837])).

fof(f1837,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f968])).

fof(f968,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f967])).

fof(f967,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f2989,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl117_24 ),
    inference(avatar_component_clause,[],[f2988])).

fof(f3359,plain,
    ( ~ spl117_59
    | ~ spl117_36
    | spl117_24 ),
    inference(avatar_split_clause,[],[f3355,f2988,f3082,f3357])).

fof(f3357,plain,
    ( spl117_59
  <=> v1_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_59])])).

fof(f3355,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(k4_relat_1(sK0))
    | spl117_24 ),
    inference(global_subsumption,[],[f1831,f1830,f3352])).

fof(f3352,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl117_24 ),
    inference(resolution,[],[f2989,f1942])).

fof(f1942,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1045])).

fof(f1045,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1044])).

fof(f1044,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f902])).

fof(f902,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f3349,plain,
    ( ~ spl117_58
    | spl117_23 ),
    inference(avatar_split_clause,[],[f3345,f2983,f3347])).

fof(f3347,plain,
    ( spl117_58
  <=> v1_xboole_0(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_58])])).

fof(f2983,plain,
    ( spl117_23
  <=> v1_xboole_0(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_23])])).

fof(f3345,plain,
    ( ~ v1_xboole_0(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl117_23 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3344])).

fof(f3344,plain,
    ( ~ v1_xboole_0(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_23 ),
    inference(superposition,[],[f2984,f1875])).

fof(f1875,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1002])).

fof(f1002,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1001])).

fof(f1001,plain,(
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

fof(f2984,plain,
    ( ~ v1_xboole_0(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl117_23 ),
    inference(avatar_component_clause,[],[f2983])).

fof(f3340,plain,
    ( ~ spl117_57
    | spl117_52 ),
    inference(avatar_split_clause,[],[f3336,f3244,f3338])).

fof(f3338,plain,
    ( spl117_57
  <=> v1_relat_1(k2_funct_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_57])])).

fof(f3244,plain,
    ( spl117_52
  <=> v1_relat_1(k2_funct_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_52])])).

fof(f3336,plain,
    ( ~ v1_relat_1(k2_funct_1(k4_relat_1(sK0)))
    | spl117_52 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3329])).

fof(f3329,plain,
    ( ~ v1_relat_1(k2_funct_1(k4_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_52 ),
    inference(superposition,[],[f3245,f1875])).

fof(f3245,plain,
    ( ~ v1_relat_1(k2_funct_1(k2_funct_1(sK0)))
    | spl117_52 ),
    inference(avatar_component_clause,[],[f3244])).

fof(f3335,plain,
    ( ~ spl117_56
    | spl117_52 ),
    inference(avatar_split_clause,[],[f3328,f3244,f3333])).

fof(f3333,plain,
    ( spl117_56
  <=> v1_xboole_0(k2_funct_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_56])])).

fof(f3328,plain,
    ( ~ v1_xboole_0(k2_funct_1(k2_funct_1(sK0)))
    | spl117_52 ),
    inference(resolution,[],[f3245,f2235])).

fof(f2235,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1233])).

fof(f1233,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f3331,plain,
    ( ~ spl117_7
    | ~ spl117_22
    | spl117_52 ),
    inference(avatar_split_clause,[],[f3327,f3244,f2977,f2884])).

fof(f2884,plain,
    ( spl117_7
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_7])])).

fof(f2977,plain,
    ( spl117_22
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_22])])).

fof(f3327,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_52 ),
    inference(resolution,[],[f3245,f1876])).

fof(f1876,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1004])).

fof(f1004,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1003])).

fof(f1003,plain,(
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

fof(f3326,plain,(
    spl117_29 ),
    inference(avatar_contradiction_clause,[],[f3321])).

fof(f3321,plain,
    ( $false
    | spl117_29 ),
    inference(resolution,[],[f3024,f1961])).

fof(f1961,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3024,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | spl117_29 ),
    inference(avatar_component_clause,[],[f3023])).

fof(f3023,plain,
    ( spl117_29
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_29])])).

fof(f3295,plain,
    ( ~ spl117_55
    | spl117_51 ),
    inference(avatar_split_clause,[],[f3291,f3241,f3293])).

fof(f3293,plain,
    ( spl117_55
  <=> v2_funct_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_55])])).

fof(f3241,plain,
    ( spl117_51
  <=> v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_51])])).

fof(f3291,plain,
    ( ~ v2_funct_1(k4_relat_1(sK0))
    | spl117_51 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3290])).

fof(f3290,plain,
    ( ~ v2_funct_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_51 ),
    inference(superposition,[],[f3242,f1875])).

fof(f3242,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    | spl117_51 ),
    inference(avatar_component_clause,[],[f3241])).

fof(f3253,plain,
    ( ~ spl117_7
    | ~ spl117_22
    | spl117_54
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3131,f2900,f3251,f2977,f2884])).

fof(f3251,plain,
    ( spl117_54
  <=> ! [X6] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK12(X6,k2_funct_1(sK0))))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),X6)
        | k2_relat_1(k2_funct_1(sK0)) = X6
        | ~ v1_relat_1(sK13(X6,k2_funct_1(sK0)))
        | k1_relat_1(sK0) != k1_relat_1(sK13(X6,k2_funct_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_54])])).

fof(f2900,plain,
    ( spl117_11
  <=> ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_11])])).

fof(f3131,plain,
    ( ! [X6] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK12(X6,k2_funct_1(sK0))))
        | k1_relat_1(sK0) != k1_relat_1(sK13(X6,k2_funct_1(sK0)))
        | ~ v1_relat_1(sK13(X6,k2_funct_1(sK0)))
        | k2_relat_1(k2_funct_1(sK0)) = X6
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),X6)
        | ~ v1_funct_1(k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f1940])).

fof(f1940,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,sK12(X0,X1)) = k5_relat_1(X1,sK13(X0,X1))
      | k2_relat_1(X1) = X0
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1540])).

fof(f1540,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ( sK12(X0,X1) != sK13(X0,X1)
        & k5_relat_1(X1,sK12(X0,X1)) = k5_relat_1(X1,sK13(X0,X1))
        & k1_relat_1(sK13(X0,X1)) = X0
        & k1_relat_1(sK12(X0,X1)) = X0
        & v1_funct_1(sK13(X0,X1))
        & v1_relat_1(sK13(X0,X1))
        & v1_funct_1(sK12(X0,X1))
        & v1_relat_1(sK12(X0,X1)) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f1043,f1539,f1538])).

fof(f1538,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ? [X3] :
            ( sK12(X0,X1) != X3
            & k5_relat_1(X1,X3) = k5_relat_1(X1,sK12(X0,X1))
            & k1_relat_1(X3) = X0
            & k1_relat_1(sK12(X0,X1)) = X0
            & v1_funct_1(X3)
            & v1_relat_1(X3) )
        & v1_funct_1(sK12(X0,X1))
        & v1_relat_1(sK12(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1539,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( sK12(X0,X1) != X3
          & k5_relat_1(X1,X3) = k5_relat_1(X1,sK12(X0,X1))
          & k1_relat_1(X3) = X0
          & k1_relat_1(sK12(X0,X1)) = X0
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( sK12(X0,X1) != sK13(X0,X1)
        & k5_relat_1(X1,sK12(X0,X1)) = k5_relat_1(X1,sK13(X0,X1))
        & k1_relat_1(sK13(X0,X1)) = X0
        & k1_relat_1(sK12(X0,X1)) = X0
        & v1_funct_1(sK13(X0,X1))
        & v1_relat_1(sK13(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1043,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1042])).

fof(f1042,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ? [X2] :
          ( ? [X3] :
              ( X2 != X3
              & k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
              & k1_relat_1(X3) = X0
              & k1_relat_1(X2) = X0
              & v1_funct_1(X3)
              & v1_relat_1(X3) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f930])).

fof(f930,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ! [X3] :
                  ( ( v1_funct_1(X3)
                    & v1_relat_1(X3) )
                 => ( ( k5_relat_1(X1,X2) = k5_relat_1(X1,X3)
                      & k1_relat_1(X3) = X0
                      & k1_relat_1(X2) = X0 )
                   => X2 = X3 ) ) )
          & r1_tarski(k2_relat_1(X1),X0) )
       => k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_funct_1)).

fof(f2901,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | ~ spl117_11 ),
    inference(avatar_component_clause,[],[f2900])).

fof(f3249,plain,
    ( ~ spl117_7
    | ~ spl117_22
    | ~ spl117_51
    | ~ spl117_52
    | ~ spl117_53
    | ~ spl117_9
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3136,f2900,f2892,f3247,f3244,f3241,f2977,f2884])).

fof(f3247,plain,
    ( spl117_53
  <=> k1_relat_1(sK0) = k1_relat_1(k2_funct_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_53])])).

fof(f2892,plain,
    ( spl117_9
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_9])])).

fof(f3136,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k2_funct_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(sK0)))
    | ~ v2_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f1871])).

fof(f1871,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f998])).

fof(f998,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f997])).

fof(f997,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f950])).

fof(f950,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f3234,plain,
    ( ~ spl117_36
    | spl117_50
    | spl117_15 ),
    inference(avatar_split_clause,[],[f3233,f2924,f3230,f3082])).

fof(f3230,plain,
    ( spl117_50
  <=> ! [X1] :
        ( k2_relat_1(X1) != k2_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(X1)
        | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_50])])).

fof(f2924,plain,
    ( spl117_15
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_15])])).

fof(f3233,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != k2_relat_1(k4_relat_1(sK0))
        | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k4_relat_1(sK0)) )
    | spl117_15 ),
    inference(global_subsumption,[],[f3228])).

fof(f3228,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != k2_relat_1(k4_relat_1(sK0))
        | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k4_relat_1(sK0)) )
    | spl117_15 ),
    inference(global_subsumption,[],[f1830,f3104])).

fof(f3104,plain,
    ( ! [X1] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0))
        | k2_relat_1(X1) != k2_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k4_relat_1(sK0)) )
    | spl117_15 ),
    inference(superposition,[],[f2925,f1840])).

fof(f1840,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f974])).

fof(f974,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f973])).

fof(f973,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f802])).

fof(f802,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f2925,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl117_15 ),
    inference(avatar_component_clause,[],[f2924])).

fof(f3232,plain,
    ( ~ spl117_36
    | spl117_50
    | spl117_15 ),
    inference(avatar_split_clause,[],[f3228,f2924,f3230,f3082])).

fof(f3227,plain,(
    spl117_36 ),
    inference(avatar_contradiction_clause,[],[f3226])).

fof(f3226,plain,
    ( $false
    | spl117_36 ),
    inference(global_subsumption,[],[f1830,f3221])).

fof(f3221,plain,
    ( ~ v1_relat_1(sK0)
    | spl117_36 ),
    inference(resolution,[],[f3083,f2166])).

fof(f2166,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1186])).

fof(f1186,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f666])).

fof(f666,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f3083,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl117_36 ),
    inference(avatar_component_clause,[],[f3082])).

fof(f3225,plain,(
    spl117_36 ),
    inference(avatar_contradiction_clause,[],[f3224])).

fof(f3224,plain,
    ( $false
    | spl117_36 ),
    inference(global_subsumption,[],[f1830,f3221])).

fof(f3219,plain,(
    spl117_22 ),
    inference(avatar_contradiction_clause,[],[f3218])).

fof(f3218,plain,
    ( $false
    | spl117_22 ),
    inference(global_subsumption,[],[f1831,f1830,f3213])).

fof(f3213,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_22 ),
    inference(resolution,[],[f2978,f1877])).

fof(f1877,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1004])).

fof(f2978,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | spl117_22 ),
    inference(avatar_component_clause,[],[f2977])).

fof(f3217,plain,(
    spl117_22 ),
    inference(avatar_contradiction_clause,[],[f3216])).

fof(f3216,plain,
    ( $false
    | spl117_22 ),
    inference(global_subsumption,[],[f1831,f1830,f3213])).

fof(f3182,plain,
    ( ~ spl117_7
    | spl117_49
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3138,f2900,f3179,f2884])).

fof(f3179,plain,
    ( spl117_49
  <=> ! [X3,X2] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X3))
        | ~ v1_relat_1(X3)
        | k1_relat_1(X2) != k1_relat_1(sK0)
        | k1_relat_1(X2) != k1_relat_1(X3)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_49])])).

fof(f3138,plain,
    ( ! [X4,X5] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X5))
        | k1_relat_1(X4) != k1_relat_1(sK0)
        | ~ v1_relat_1(X4)
        | k1_relat_1(X4) != k1_relat_1(X5)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X5) )
    | ~ spl117_11 ),
    inference(duplicate_literal_removal,[],[f3135])).

fof(f3135,plain,
    ( ! [X4,X5] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X5))
        | k1_relat_1(X4) != k1_relat_1(sK0)
        | ~ v1_relat_1(X4)
        | k1_relat_1(X4) != k1_relat_1(X5)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f1839])).

fof(f1839,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f972])).

fof(f972,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X1) != k1_relat_1(X0)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f971])).

fof(f971,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X1) != k1_relat_1(X0)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f801])).

fof(f801,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X1) = k1_relat_1(X0)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f3181,plain,
    ( ~ spl117_7
    | spl117_49
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3139,f2900,f3179,f2884])).

fof(f3139,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X3))
        | k1_relat_1(X2) != k1_relat_1(sK0)
        | ~ v1_relat_1(X2)
        | k1_relat_1(X2) != k1_relat_1(X3)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X3) )
    | ~ spl117_11 ),
    inference(duplicate_literal_removal,[],[f3134])).

fof(f3134,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X3))
        | k1_relat_1(X2) != k1_relat_1(sK0)
        | ~ v1_relat_1(X2)
        | k1_relat_1(X2) != k1_relat_1(X3)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3) )
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f1839])).

fof(f3177,plain,
    ( ~ spl117_7
    | spl117_48
    | ~ spl117_9
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3140,f2900,f2892,f3175,f2884])).

fof(f3175,plain,
    ( spl117_48
  <=> ! [X1] :
        ( k1_relat_1(X1) != k1_relat_1(sK0)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_48])])).

fof(f3140,plain,
    ( ! [X1] :
        ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
        | k1_relat_1(X1) != k1_relat_1(sK0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(X1))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(duplicate_literal_removal,[],[f3133])).

fof(f3133,plain,
    ( ! [X1] :
        ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
        | k1_relat_1(X1) != k1_relat_1(sK0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f1847])).

fof(f1847,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f985])).

fof(f985,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f984])).

fof(f984,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f845])).

fof(f845,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f3173,plain,
    ( ~ spl117_7
    | spl117_47
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3141,f2900,f3171,f2884])).

fof(f3171,plain,
    ( spl117_47
  <=> ! [X0] :
        ( k2_relat_1(sK0) != k10_relat_1(k2_funct_1(sK0),k1_relat_1(X0))
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_47])])).

fof(f3141,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k10_relat_1(k2_funct_1(sK0),k1_relat_1(X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(duplicate_literal_removal,[],[f3132])).

fof(f3132,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k10_relat_1(k2_funct_1(sK0),k1_relat_1(X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f2584])).

fof(f2584,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1379])).

fof(f1379,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f784])).

fof(f784,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f3169,plain,
    ( ~ spl117_7
    | spl117_46
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3130,f2900,f3167,f2884])).

fof(f3167,plain,
    ( spl117_46
  <=> ! [X5,X4] :
        ( k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X4,k5_relat_1(k2_funct_1(sK0),X5)))
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(k8_relat_1(X4,X5))
        | k1_relat_1(sK0) != k1_relat_1(k8_relat_1(X4,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_46])])).

fof(f3130,plain,
    ( ! [X4,X5] :
        ( k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X4,k5_relat_1(k2_funct_1(sK0),X5)))
        | k1_relat_1(sK0) != k1_relat_1(k8_relat_1(X4,X5))
        | ~ v1_relat_1(k8_relat_1(X4,X5))
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f2665])).

fof(f2665,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1464])).

fof(f1464,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f742])).

fof(f742,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f3165,plain,
    ( ~ spl117_7
    | spl117_45
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3129,f2900,f3163,f2884])).

fof(f3163,plain,
    ( spl117_45
  <=> ! [X3,X2] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X2))
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(k7_relat_1(X2,X3)))
        | ~ v1_relat_1(k7_relat_1(X2,X3))
        | k1_relat_1(sK0) != k1_relat_1(k7_relat_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_45])])).

fof(f3129,plain,
    ( ! [X2,X3] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X2))
        | k1_relat_1(sK0) != k1_relat_1(k7_relat_1(X2,X3))
        | ~ v1_relat_1(k7_relat_1(X2,X3))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(k7_relat_1(X2,X3)))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f2618])).

fof(f2618,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1417])).

fof(f1417,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1416])).

fof(f1416,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f804])).

fof(f804,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
           => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).

fof(f3161,plain,
    ( ~ spl117_7
    | ~ spl117_43
    | ~ spl117_9
    | ~ spl117_44
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3154,f2900,f3159,f2892,f3156,f2884])).

fof(f3156,plain,
    ( spl117_43
  <=> v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_43])])).

fof(f3159,plain,
    ( spl117_44
  <=> k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_44])])).

fof(f3154,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k2_funct_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl117_11 ),
    inference(forward_demodulation,[],[f3128,f2197])).

fof(f2197,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f3128,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f2196])).

fof(f2196,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1207])).

fof(f1207,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f872])).

fof(f872,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f3153,plain,
    ( ~ spl117_7
    | ~ spl117_9
    | spl117_42
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3149,f2900,f3151,f2892,f2884])).

fof(f3151,plain,
    ( spl117_42
  <=> ! [X1] :
        ( k1_relat_1(sK0) != X1
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),X1)
        | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_42])])).

fof(f3149,plain,
    ( ! [X1] :
        ( k1_relat_1(sK0) != X1
        | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),X1)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(forward_demodulation,[],[f3127,f2197])).

fof(f3127,plain,
    ( ! [X1] :
        ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
        | k1_relat_1(sK0) != k1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),X1)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f2188])).

fof(f2188,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1200])).

fof(f1200,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1199])).

fof(f1199,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f871])).

fof(f871,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f3148,plain,
    ( ~ spl117_7
    | spl117_41
    | ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3144,f2900,f3146,f2884])).

fof(f3146,plain,
    ( spl117_41
  <=> ! [X0] :
        ( k1_relat_1(sK0) != X0
        | ~ v1_relat_1(k6_relat_1(X0))
        | k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X0,k2_funct_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_41])])).

fof(f3144,plain,
    ( ! [X0] :
        ( k1_relat_1(sK0) != X0
        | k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X0,k2_funct_1(sK0)))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(forward_demodulation,[],[f3126,f2197])).

fof(f3126,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k8_relat_1(X0,k2_funct_1(sK0)))
        | k1_relat_1(k6_relat_1(X0)) != k1_relat_1(sK0)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | ~ spl117_11 ),
    inference(superposition,[],[f2901,f2192])).

fof(f2192,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1203])).

fof(f1203,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f726])).

fof(f726,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f3122,plain,
    ( ~ spl117_40
    | spl117_18 ),
    inference(avatar_split_clause,[],[f3118,f2950,f3120])).

fof(f3120,plain,
    ( spl117_40
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_40])])).

fof(f2950,plain,
    ( spl117_18
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_18])])).

fof(f3118,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
    | spl117_18 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3108])).

fof(f3108,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_18 ),
    inference(superposition,[],[f2951,f1874])).

fof(f2951,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | spl117_18 ),
    inference(avatar_component_clause,[],[f2950])).

fof(f3117,plain,
    ( ~ spl117_39
    | spl117_18 ),
    inference(avatar_split_clause,[],[f3113,f2950,f3115])).

fof(f3115,plain,
    ( spl117_39
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_39])])).

fof(f3113,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0)))
    | spl117_18 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3107])).

fof(f3107,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k4_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_18 ),
    inference(superposition,[],[f2951,f1875])).

fof(f3100,plain,
    ( ~ spl117_38
    | spl117_20 ),
    inference(avatar_split_clause,[],[f3096,f2968,f3098])).

fof(f3098,plain,
    ( spl117_38
  <=> v1_xboole_0(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_38])])).

fof(f2968,plain,
    ( spl117_20
  <=> v1_xboole_0(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_20])])).

fof(f3096,plain,
    ( ~ v1_xboole_0(k4_relat_1(sK0))
    | spl117_20 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3095])).

fof(f3095,plain,
    ( ~ v1_xboole_0(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_20 ),
    inference(superposition,[],[f2969,f1875])).

fof(f2969,plain,
    ( ~ v1_xboole_0(k2_funct_1(sK0))
    | spl117_20 ),
    inference(avatar_component_clause,[],[f2968])).

fof(f3091,plain,
    ( ~ spl117_36
    | spl117_37
    | spl117_6 ),
    inference(avatar_split_clause,[],[f3090,f2879,f3087,f3082])).

fof(f3087,plain,
    ( spl117_37
  <=> ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK0)
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_37])])).

fof(f2879,plain,
    ( spl117_6
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_6])])).

fof(f3090,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),X1))
        | k1_relat_1(X1) != k1_relat_1(sK0)
        | ~ v1_relat_1(k4_relat_1(sK0)) )
    | spl117_6 ),
    inference(global_subsumption,[],[f3085])).

fof(f3085,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(X0)
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0)) )
    | spl117_6 ),
    inference(global_subsumption,[],[f1830,f3074])).

fof(f3074,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl117_6 ),
    inference(superposition,[],[f2880,f1839])).

fof(f2880,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl117_6 ),
    inference(avatar_component_clause,[],[f2879])).

fof(f3089,plain,
    ( ~ spl117_36
    | spl117_37
    | spl117_6 ),
    inference(avatar_split_clause,[],[f3085,f2879,f3087,f3082])).

fof(f3084,plain,
    ( ~ spl117_35
    | ~ spl117_36
    | spl117_6 ),
    inference(avatar_split_clause,[],[f3077,f2879,f3082,f3079])).

fof(f3079,plain,
    ( spl117_35
  <=> k2_relat_1(sK0) = k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_35])])).

fof(f3077,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | spl117_6 ),
    inference(global_subsumption,[],[f1830,f3072])).

fof(f3072,plain,
    ( k2_relat_1(sK0) != k10_relat_1(k4_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl117_6 ),
    inference(superposition,[],[f2880,f2584])).

fof(f3063,plain,
    ( ~ spl117_12
    | ~ spl117_34
    | spl117_13 ),
    inference(avatar_split_clause,[],[f3042,f2909,f3061,f2906])).

fof(f2906,plain,
    ( spl117_12
  <=> v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_12])])).

fof(f3061,plain,
    ( spl117_34
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_34])])).

fof(f2909,plain,
    ( spl117_13
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_13])])).

fof(f3042,plain,
    ( k1_xboole_0 != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl117_13 ),
    inference(trivial_inequality_removal,[],[f3041])).

fof(f3041,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl117_13 ),
    inference(superposition,[],[f2910,f1885])).

fof(f1885,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1522])).

fof(f1522,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1015])).

fof(f1015,plain,(
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

fof(f2910,plain,
    ( k1_xboole_0 != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl117_13 ),
    inference(avatar_component_clause,[],[f2909])).

fof(f3059,plain,
    ( ~ spl117_7
    | spl117_33
    | spl117_13 ),
    inference(avatar_split_clause,[],[f3058,f2909,f3055,f2884])).

fof(f3055,plain,
    ( spl117_33
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_33])])).

fof(f3058,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_relat_1(k5_relat_1(X1,sK0))
        | ~ v1_relat_1(X1)
        | k2_relat_1(X1) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | spl117_13 ),
    inference(global_subsumption,[],[f3053])).

fof(f3053,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | k1_xboole_0 != k2_relat_1(k5_relat_1(X0,sK0))
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | spl117_13 ),
    inference(global_subsumption,[],[f1830,f3039])).

fof(f3039,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(k5_relat_1(X0,sK0))
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X0) )
    | spl117_13 ),
    inference(superposition,[],[f2910,f1840])).

fof(f3057,plain,
    ( ~ spl117_7
    | spl117_33
    | spl117_13 ),
    inference(avatar_split_clause,[],[f3053,f2909,f3055,f2884])).

fof(f3052,plain,
    ( ~ spl117_32
    | ~ spl117_7
    | spl117_13 ),
    inference(avatar_split_clause,[],[f3048,f2909,f2884,f3050])).

fof(f3050,plain,
    ( spl117_32
  <=> k1_xboole_0 = k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_32])])).

fof(f3048,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | k1_xboole_0 != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | spl117_13 ),
    inference(global_subsumption,[],[f1830,f3037])).

fof(f3037,plain,
    ( k1_xboole_0 != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_13 ),
    inference(superposition,[],[f2910,f2558])).

fof(f2558,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1359])).

fof(f1359,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f764])).

fof(f764,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f3047,plain,
    ( ~ spl117_31
    | spl117_13 ),
    inference(avatar_split_clause,[],[f3043,f2909,f3045])).

fof(f3045,plain,
    ( spl117_31
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_31])])).

fof(f3043,plain,
    ( k1_xboole_0 != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl117_13 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3036])).

fof(f3036,plain,
    ( k1_xboole_0 != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_13 ),
    inference(superposition,[],[f2910,f1875])).

fof(f3035,plain,
    ( ~ spl117_30
    | spl117_17 ),
    inference(avatar_split_clause,[],[f3031,f2945,f3033])).

fof(f3033,plain,
    ( spl117_30
  <=> r1_tarski(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_30])])).

fof(f3031,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0)))
    | spl117_17 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3028])).

fof(f3028,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0)))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_17 ),
    inference(superposition,[],[f2946,f1875])).

fof(f3025,plain,
    ( ~ spl117_7
    | ~ spl117_28
    | ~ spl117_29
    | spl117_10 ),
    inference(avatar_split_clause,[],[f3007,f2895,f3023,f3020,f2884])).

fof(f3020,plain,
    ( spl117_28
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_28])])).

fof(f2895,plain,
    ( spl117_10
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_10])])).

fof(f3007,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK0))
    | k1_xboole_0 != k1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_10 ),
    inference(superposition,[],[f2896,f1885])).

fof(f2896,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | spl117_10 ),
    inference(avatar_component_clause,[],[f2895])).

fof(f3018,plain,
    ( ~ spl117_27
    | spl117_10 ),
    inference(avatar_split_clause,[],[f3014,f2895,f3016])).

fof(f3014,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl117_10 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3006])).

fof(f3006,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_10 ),
    inference(superposition,[],[f2896,f1874])).

fof(f3013,plain,
    ( ~ spl117_26
    | spl117_10 ),
    inference(avatar_split_clause,[],[f3009,f2895,f3011])).

fof(f3011,plain,
    ( spl117_26
  <=> r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_26])])).

fof(f3009,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | spl117_10 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f3005])).

fof(f3005,plain,
    ( ~ r1_tarski(k2_relat_1(k4_relat_1(sK0)),k1_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_10 ),
    inference(superposition,[],[f2896,f1875])).

fof(f3003,plain,(
    spl117_9 ),
    inference(avatar_contradiction_clause,[],[f3002])).

fof(f3002,plain,
    ( $false
    | spl117_9 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f2996])).

fof(f2996,plain,
    ( ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_9 ),
    inference(trivial_inequality_removal,[],[f2992])).

fof(f2992,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_9 ),
    inference(superposition,[],[f2893,f1873])).

fof(f1873,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1000])).

fof(f2893,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | spl117_9 ),
    inference(avatar_component_clause,[],[f2892])).

fof(f3001,plain,
    ( ~ spl117_25
    | spl117_9 ),
    inference(avatar_split_clause,[],[f2997,f2892,f2999])).

fof(f2999,plain,
    ( spl117_25
  <=> k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_25])])).

fof(f2997,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | spl117_9 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f2991])).

fof(f2991,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_9 ),
    inference(superposition,[],[f2893,f1875])).

fof(f2990,plain,
    ( ~ spl117_24
    | spl117_12 ),
    inference(avatar_split_clause,[],[f2986,f2906,f2988])).

fof(f2986,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl117_12 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f2965])).

fof(f2965,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_12 ),
    inference(superposition,[],[f2907,f1875])).

fof(f2907,plain,
    ( ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl117_12 ),
    inference(avatar_component_clause,[],[f2906])).

fof(f2985,plain,
    ( ~ spl117_23
    | spl117_12 ),
    inference(avatar_split_clause,[],[f2964,f2906,f2983])).

fof(f2964,plain,
    ( ~ v1_xboole_0(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl117_12 ),
    inference(resolution,[],[f2907,f2235])).

fof(f2981,plain,
    ( ~ spl117_7
    | spl117_12 ),
    inference(avatar_split_clause,[],[f2980,f2906,f2884])).

fof(f2980,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_12 ),
    inference(global_subsumption,[],[f1830,f2963])).

fof(f2963,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_12 ),
    inference(resolution,[],[f2907,f1837])).

fof(f2979,plain,
    ( ~ spl117_7
    | ~ spl117_22
    | spl117_12 ),
    inference(avatar_split_clause,[],[f2975,f2906,f2977,f2884])).

fof(f2975,plain,
    ( ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_12 ),
    inference(global_subsumption,[],[f1831,f1830,f2962])).

fof(f2962,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_12 ),
    inference(resolution,[],[f2907,f1942])).

fof(f2974,plain,
    ( ~ spl117_21
    | ~ spl117_7
    | spl117_12 ),
    inference(avatar_split_clause,[],[f2961,f2906,f2884,f2972])).

fof(f2972,plain,
    ( spl117_21
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_21])])).

fof(f2961,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_xboole_0(sK0)
    | spl117_12 ),
    inference(resolution,[],[f2907,f2212])).

fof(f2212,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1214])).

fof(f1214,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1213])).

fof(f1213,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_relat_1)).

fof(f2970,plain,
    ( ~ spl117_20
    | spl117_12 ),
    inference(avatar_split_clause,[],[f2966,f2906,f2968])).

fof(f2966,plain,
    ( ~ v1_xboole_0(k2_funct_1(sK0))
    | spl117_12 ),
    inference(global_subsumption,[],[f1830,f2960])).

fof(f2960,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_xboole_0(k2_funct_1(sK0))
    | spl117_12 ),
    inference(resolution,[],[f2907,f2214])).

fof(f2214,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1216])).

fof(f1216,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1215])).

fof(f1215,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_relat_1)).

fof(f2959,plain,
    ( ~ spl117_19
    | spl117_14 ),
    inference(avatar_split_clause,[],[f2955,f2912,f2957])).

fof(f2957,plain,
    ( spl117_19
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_19])])).

fof(f2912,plain,
    ( spl117_14
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_14])])).

fof(f2955,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | spl117_14 ),
    inference(global_subsumption,[],[f1830,f2954])).

fof(f2954,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_14 ),
    inference(trivial_inequality_removal,[],[f2953])).

fof(f2953,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_14 ),
    inference(superposition,[],[f2913,f1885])).

fof(f2913,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | spl117_14 ),
    inference(avatar_component_clause,[],[f2912])).

fof(f2952,plain,
    ( ~ spl117_7
    | ~ spl117_18
    | spl117_2 ),
    inference(avatar_split_clause,[],[f2948,f2856,f2950,f2884])).

fof(f2856,plain,
    ( spl117_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_2])])).

fof(f2948,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_2 ),
    inference(global_subsumption,[],[f1830,f2916])).

fof(f2916,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_2 ),
    inference(superposition,[],[f2857,f2558])).

fof(f2857,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl117_2 ),
    inference(avatar_component_clause,[],[f2856])).

fof(f2947,plain,
    ( ~ spl117_17
    | ~ spl117_7
    | spl117_2 ),
    inference(avatar_split_clause,[],[f2943,f2856,f2884,f2945])).

fof(f2943,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | spl117_2 ),
    inference(global_subsumption,[],[f1830,f2921])).

fof(f2921,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl117_2 ),
    inference(trivial_inequality_removal,[],[f2917])).

fof(f2917,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | ~ r1_tarski(k1_relat_1(sK0),k2_relat_1(k2_funct_1(sK0)))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl117_2 ),
    inference(superposition,[],[f2857,f1846])).

fof(f1846,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f983])).

fof(f983,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f982])).

fof(f982,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f846])).

fof(f846,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f2942,plain,
    ( ~ spl117_7
    | spl117_16
    | spl117_2 ),
    inference(avatar_split_clause,[],[f2941,f2856,f2938,f2884])).

fof(f2938,plain,
    ( spl117_16
  <=> ! [X1] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0))
        | k2_relat_1(X1) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_16])])).

fof(f2941,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(X0) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(k2_funct_1(sK0))
        | k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X0,sK0)) )
    | spl117_2 ),
    inference(global_subsumption,[],[f2936])).

fof(f2936,plain,
    ( ! [X1] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | k2_relat_1(X1) != k2_relat_1(k2_funct_1(sK0)) )
    | spl117_2 ),
    inference(global_subsumption,[],[f1830,f2919])).

fof(f2919,plain,
    ( ! [X1] :
        ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(X1,sK0))
        | k2_relat_1(X1) != k2_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k2_funct_1(sK0)) )
    | spl117_2 ),
    inference(superposition,[],[f2857,f1840])).

fof(f2940,plain,
    ( ~ spl117_7
    | spl117_16
    | spl117_2 ),
    inference(avatar_split_clause,[],[f2936,f2856,f2938,f2884])).

fof(f2935,plain,(
    spl117_7 ),
    inference(avatar_contradiction_clause,[],[f2934])).

fof(f2934,plain,
    ( $false
    | spl117_7 ),
    inference(global_subsumption,[],[f1831,f1830,f2927])).

fof(f2927,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_7 ),
    inference(resolution,[],[f2885,f1876])).

fof(f2885,plain,
    ( ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_7 ),
    inference(avatar_component_clause,[],[f2884])).

fof(f2933,plain,(
    spl117_7 ),
    inference(avatar_contradiction_clause,[],[f2932])).

fof(f2932,plain,
    ( $false
    | spl117_7 ),
    inference(global_subsumption,[],[f1831,f1830,f2927])).

fof(f2931,plain,(
    spl117_7 ),
    inference(avatar_contradiction_clause,[],[f2930])).

fof(f2930,plain,
    ( $false
    | spl117_7 ),
    inference(global_subsumption,[],[f1831,f1830,f2927])).

fof(f2926,plain,
    ( ~ spl117_15
    | spl117_2 ),
    inference(avatar_split_clause,[],[f2922,f2856,f2924])).

fof(f2922,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl117_2 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f2915])).

fof(f2915,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_2 ),
    inference(superposition,[],[f2857,f1875])).

fof(f2914,plain,
    ( ~ spl117_12
    | ~ spl117_13
    | ~ spl117_14
    | spl117_1 ),
    inference(avatar_split_clause,[],[f2876,f2853,f2912,f2909,f2906])).

fof(f2853,plain,
    ( spl117_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_1])])).

fof(f2876,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ v1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl117_1 ),
    inference(superposition,[],[f2854,f1886])).

fof(f1886,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1522])).

fof(f2854,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | spl117_1 ),
    inference(avatar_component_clause,[],[f2853])).

fof(f2904,plain,
    ( spl117_11
    | ~ spl117_7
    | spl117_1 ),
    inference(avatar_split_clause,[],[f2903,f2853,f2884,f2900])).

fof(f2903,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(X1)
        | k1_relat_1(X1) != k1_relat_1(sK0)
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X1)) )
    | spl117_1 ),
    inference(global_subsumption,[],[f2898])).

fof(f2898,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | k1_relat_1(X0) != k1_relat_1(sK0) )
    | spl117_1 ),
    inference(global_subsumption,[],[f1830,f2874])).

fof(f2874,plain,
    ( ! [X0] :
        ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),X0))
        | k1_relat_1(X0) != k1_relat_1(sK0)
        | ~ v1_relat_1(k2_funct_1(sK0))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0) )
    | spl117_1 ),
    inference(superposition,[],[f2854,f1839])).

fof(f2902,plain,
    ( ~ spl117_7
    | spl117_11
    | spl117_1 ),
    inference(avatar_split_clause,[],[f2898,f2853,f2900,f2884])).

fof(f2897,plain,
    ( ~ spl117_9
    | ~ spl117_7
    | ~ spl117_10
    | spl117_1 ),
    inference(avatar_split_clause,[],[f2890,f2853,f2895,f2884,f2892])).

fof(f2890,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | spl117_1 ),
    inference(global_subsumption,[],[f1830,f2873])).

fof(f2873,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k2_funct_1(sK0))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_1 ),
    inference(superposition,[],[f2854,f1847])).

fof(f2889,plain,
    ( ~ spl117_7
    | ~ spl117_8
    | spl117_1 ),
    inference(avatar_split_clause,[],[f2882,f2853,f2887,f2884])).

fof(f2887,plain,
    ( spl117_8
  <=> k2_relat_1(sK0) = k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_8])])).

fof(f2882,plain,
    ( k2_relat_1(sK0) != k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_1 ),
    inference(global_subsumption,[],[f1830,f2872])).

fof(f2872,plain,
    ( k2_relat_1(sK0) != k10_relat_1(k2_funct_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK0))
    | spl117_1 ),
    inference(superposition,[],[f2854,f2584])).

fof(f2881,plain,
    ( ~ spl117_6
    | spl117_1 ),
    inference(avatar_split_clause,[],[f2877,f2853,f2879])).

fof(f2877,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | spl117_1 ),
    inference(global_subsumption,[],[f1832,f1831,f1830,f2871])).

fof(f2871,plain,
    ( k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k4_relat_1(sK0),sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl117_1 ),
    inference(superposition,[],[f2854,f1875])).

fof(f2870,plain,(
    spl117_5 ),
    inference(avatar_split_clause,[],[f1830,f2868])).

fof(f2868,plain,
    ( spl117_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_5])])).

fof(f2866,plain,(
    spl117_4 ),
    inference(avatar_split_clause,[],[f1831,f2864])).

fof(f2864,plain,
    ( spl117_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_4])])).

fof(f2862,plain,(
    spl117_3 ),
    inference(avatar_split_clause,[],[f1832,f2860])).

fof(f2860,plain,
    ( spl117_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_3])])).

fof(f2858,plain,
    ( ~ spl117_1
    | ~ spl117_2 ),
    inference(avatar_split_clause,[],[f1833,f2856,f2853])).

fof(f1833,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f1512])).
%------------------------------------------------------------------------------
