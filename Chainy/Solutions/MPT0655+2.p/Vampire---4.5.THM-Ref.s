%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0655+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:42 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 103 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  187 ( 339 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3076,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2692,f2697,f2702,f2707,f2770,f2775,f3062])).

fof(f3062,plain,
    ( ~ spl135_1
    | ~ spl135_2
    | ~ spl135_3
    | spl135_4
    | ~ spl135_15
    | ~ spl135_16 ),
    inference(avatar_contradiction_clause,[],[f3061])).

fof(f3061,plain,
    ( $false
    | ~ spl135_1
    | ~ spl135_2
    | ~ spl135_3
    | spl135_4
    | ~ spl135_15
    | ~ spl135_16 ),
    inference(subsumption_resolution,[],[f3060,f2971])).

fof(f2971,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k2_relat_1(sK0))
    | ~ spl135_1
    | ~ spl135_2
    | ~ spl135_3 ),
    inference(unit_resulting_resolution,[],[f2691,f2696,f2701,f1760])).

fof(f1760,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f975])).

fof(f975,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f974])).

fof(f974,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f953])).

fof(f953,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f2701,plain,
    ( v2_funct_1(sK0)
    | ~ spl135_3 ),
    inference(avatar_component_clause,[],[f2699])).

fof(f2699,plain,
    ( spl135_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_3])])).

fof(f2696,plain,
    ( v1_funct_1(sK0)
    | ~ spl135_2 ),
    inference(avatar_component_clause,[],[f2694])).

fof(f2694,plain,
    ( spl135_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_2])])).

fof(f2691,plain,
    ( v1_relat_1(sK0)
    | ~ spl135_1 ),
    inference(avatar_component_clause,[],[f2689])).

fof(f2689,plain,
    ( spl135_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_1])])).

fof(f3060,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k2_relat_1(sK0))
    | ~ spl135_1
    | ~ spl135_2
    | ~ spl135_3
    | spl135_4
    | ~ spl135_15
    | ~ spl135_16 ),
    inference(forward_demodulation,[],[f3044,f2821])).

fof(f2821,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | ~ spl135_1
    | ~ spl135_2
    | ~ spl135_3 ),
    inference(unit_resulting_resolution,[],[f2691,f2696,f2701,f1765])).

fof(f1765,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f981])).

fof(f981,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f980])).

fof(f980,plain,(
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

fof(f3044,plain,
    ( k5_relat_1(k2_funct_1(sK0),sK0) != k6_relat_1(k1_relat_1(k2_funct_1(sK0)))
    | ~ spl135_1
    | ~ spl135_2
    | spl135_4
    | ~ spl135_15
    | ~ spl135_16 ),
    inference(unit_resulting_resolution,[],[f2691,f2696,f2769,f2774,f2706,f1794])).

fof(f1794,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1001])).

fof(f1001,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1000])).

fof(f1000,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f945])).

fof(f945,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f2706,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    | spl135_4 ),
    inference(avatar_component_clause,[],[f2704])).

fof(f2704,plain,
    ( spl135_4
  <=> v2_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_4])])).

fof(f2774,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl135_16 ),
    inference(avatar_component_clause,[],[f2772])).

fof(f2772,plain,
    ( spl135_16
  <=> v1_funct_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_16])])).

fof(f2769,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl135_15 ),
    inference(avatar_component_clause,[],[f2767])).

fof(f2767,plain,
    ( spl135_15
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl135_15])])).

fof(f2775,plain,
    ( spl135_16
    | ~ spl135_1
    | ~ spl135_2 ),
    inference(avatar_split_clause,[],[f2762,f2694,f2689,f2772])).

fof(f2762,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ spl135_1
    | ~ spl135_2 ),
    inference(unit_resulting_resolution,[],[f2691,f2696,f1769])).

fof(f1769,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f985])).

fof(f985,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f984])).

fof(f984,plain,(
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

fof(f2770,plain,
    ( spl135_15
    | ~ spl135_1
    | ~ spl135_2 ),
    inference(avatar_split_clause,[],[f2758,f2694,f2689,f2767])).

fof(f2758,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl135_1
    | ~ spl135_2 ),
    inference(unit_resulting_resolution,[],[f2691,f2696,f1768])).

fof(f1768,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f985])).

fof(f2707,plain,(
    ~ spl135_4 ),
    inference(avatar_split_clause,[],[f1736,f2704])).

fof(f1736,plain,(
    ~ v2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f1435])).

fof(f1435,plain,
    ( ~ v2_funct_1(k2_funct_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f965,f1434])).

fof(f1434,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(k2_funct_1(X0))
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(k2_funct_1(sK0))
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f965,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f964])).

fof(f964,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f955])).

fof(f955,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f954])).

fof(f954,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

fof(f2702,plain,(
    spl135_3 ),
    inference(avatar_split_clause,[],[f1735,f2699])).

fof(f1735,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1435])).

fof(f2697,plain,(
    spl135_2 ),
    inference(avatar_split_clause,[],[f1734,f2694])).

fof(f1734,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1435])).

fof(f2692,plain,(
    spl135_1 ),
    inference(avatar_split_clause,[],[f1733,f2689])).

fof(f1733,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1435])).
%------------------------------------------------------------------------------
