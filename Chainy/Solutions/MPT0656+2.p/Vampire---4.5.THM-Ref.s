%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0656+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 5.54s
% Output     : Refutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 142 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  270 ( 730 expanded)
%              Number of equality atoms :   70 ( 235 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8737,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2802,f2807,f2812,f2822,f2827,f2832,f2847,f3034,f7343])).

fof(f7343,plain,
    ( ~ spl136_1
    | ~ spl136_2
    | ~ spl136_3
    | ~ spl136_5
    | spl136_6
    | ~ spl136_7
    | ~ spl136_10
    | ~ spl136_25 ),
    inference(avatar_contradiction_clause,[],[f7342])).

fof(f7342,plain,
    ( $false
    | ~ spl136_1
    | ~ spl136_2
    | ~ spl136_3
    | ~ spl136_5
    | spl136_6
    | ~ spl136_7
    | ~ spl136_10
    | ~ spl136_25 ),
    inference(subsumption_resolution,[],[f7341,f2826])).

fof(f2826,plain,
    ( k2_funct_1(sK0) != sK1
    | spl136_6 ),
    inference(avatar_component_clause,[],[f2824])).

fof(f2824,plain,
    ( spl136_6
  <=> k2_funct_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl136_6])])).

fof(f7341,plain,
    ( k2_funct_1(sK0) = sK1
    | ~ spl136_1
    | ~ spl136_2
    | ~ spl136_3
    | ~ spl136_5
    | ~ spl136_7
    | ~ spl136_10
    | ~ spl136_25 ),
    inference(forward_demodulation,[],[f7340,f3038])).

fof(f3038,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl136_3 ),
    inference(unit_resulting_resolution,[],[f2811,f1847])).

fof(f1847,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f1013])).

fof(f1013,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f870])).

fof(f870,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f2811,plain,
    ( v1_relat_1(sK1)
    | ~ spl136_3 ),
    inference(avatar_component_clause,[],[f2809])).

fof(f2809,plain,
    ( spl136_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl136_3])])).

fof(f7340,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)
    | ~ spl136_1
    | ~ spl136_2
    | ~ spl136_3
    | ~ spl136_5
    | ~ spl136_7
    | ~ spl136_10
    | ~ spl136_25 ),
    inference(forward_demodulation,[],[f7339,f3532])).

fof(f3532,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1))
    | ~ spl136_1
    | ~ spl136_2
    | ~ spl136_5
    | ~ spl136_10
    | ~ spl136_25 ),
    inference(forward_demodulation,[],[f3523,f2846])).

fof(f2846,plain,
    ( k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    | ~ spl136_10 ),
    inference(avatar_component_clause,[],[f2844])).

fof(f2844,plain,
    ( spl136_10
  <=> k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl136_10])])).

fof(f3523,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl136_1
    | ~ spl136_2
    | ~ spl136_5
    | ~ spl136_25 ),
    inference(backward_demodulation,[],[f3115,f3521])).

fof(f3521,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ spl136_1
    | ~ spl136_2
    | ~ spl136_5 ),
    inference(unit_resulting_resolution,[],[f2801,f2806,f2821,f1815])).

fof(f1815,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f985])).

fof(f985,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f984])).

fof(f984,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f950])).

fof(f950,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f2821,plain,
    ( v2_funct_1(sK0)
    | ~ spl136_5 ),
    inference(avatar_component_clause,[],[f2819])).

fof(f2819,plain,
    ( spl136_5
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl136_5])])).

fof(f2806,plain,
    ( v1_funct_1(sK0)
    | ~ spl136_2 ),
    inference(avatar_component_clause,[],[f2804])).

fof(f2804,plain,
    ( spl136_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl136_2])])).

fof(f2801,plain,
    ( v1_relat_1(sK0)
    | ~ spl136_1 ),
    inference(avatar_component_clause,[],[f2799])).

fof(f2799,plain,
    ( spl136_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl136_1])])).

fof(f3115,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl136_25 ),
    inference(unit_resulting_resolution,[],[f3033,f1848])).

fof(f1848,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f1014])).

fof(f1014,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f872])).

fof(f872,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f3033,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl136_25 ),
    inference(avatar_component_clause,[],[f3031])).

fof(f3031,plain,
    ( spl136_25
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl136_25])])).

fof(f7339,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1))
    | ~ spl136_1
    | ~ spl136_2
    | ~ spl136_3
    | ~ spl136_5
    | ~ spl136_7
    | ~ spl136_25 ),
    inference(forward_demodulation,[],[f6797,f3793])).

fof(f3793,plain,
    ( k6_relat_1(k1_relat_1(sK1)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl136_1
    | ~ spl136_2
    | ~ spl136_5
    | ~ spl136_7 ),
    inference(forward_demodulation,[],[f3791,f2831])).

fof(f2831,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl136_7 ),
    inference(avatar_component_clause,[],[f2829])).

fof(f2829,plain,
    ( spl136_7
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl136_7])])).

fof(f3791,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ spl136_1
    | ~ spl136_2
    | ~ spl136_5 ),
    inference(unit_resulting_resolution,[],[f2801,f2806,f2821,f1809])).

fof(f1809,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f979])).

fof(f979,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f978])).

fof(f978,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f956])).

fof(f956,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f6797,plain,
    ( k5_relat_1(k2_funct_1(sK0),k5_relat_1(sK0,sK1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1)
    | ~ spl136_1
    | ~ spl136_3
    | ~ spl136_25 ),
    inference(unit_resulting_resolution,[],[f3033,f2801,f2811,f1863])).

fof(f1863,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1029])).

fof(f1029,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f854])).

fof(f854,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f3034,plain,
    ( spl136_25
    | ~ spl136_1
    | ~ spl136_2 ),
    inference(avatar_split_clause,[],[f2929,f2804,f2799,f3031])).

fof(f2929,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl136_1
    | ~ spl136_2 ),
    inference(unit_resulting_resolution,[],[f2801,f2806,f1818])).

fof(f1818,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f991])).

fof(f991,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f990])).

fof(f990,plain,(
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

fof(f2847,plain,(
    spl136_10 ),
    inference(avatar_split_clause,[],[f1784,f2844])).

fof(f1784,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f1478])).

fof(f1478,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f969,f1477,f1476])).

fof(f1476,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1477,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f969,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f968])).

fof(f968,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f959])).

fof(f959,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f958])).

fof(f958,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f2832,plain,(
    spl136_7 ),
    inference(avatar_split_clause,[],[f1783,f2829])).

fof(f1783,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1478])).

fof(f2827,plain,(
    ~ spl136_6 ),
    inference(avatar_split_clause,[],[f1785,f2824])).

fof(f1785,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f1478])).

fof(f2822,plain,(
    spl136_5 ),
    inference(avatar_split_clause,[],[f1782,f2819])).

fof(f1782,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1478])).

fof(f2812,plain,(
    spl136_3 ),
    inference(avatar_split_clause,[],[f1780,f2809])).

fof(f1780,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1478])).

fof(f2807,plain,(
    spl136_2 ),
    inference(avatar_split_clause,[],[f1779,f2804])).

fof(f1779,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f1478])).

fof(f2802,plain,(
    spl136_1 ),
    inference(avatar_split_clause,[],[f1778,f2799])).

fof(f1778,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f1478])).
%------------------------------------------------------------------------------
