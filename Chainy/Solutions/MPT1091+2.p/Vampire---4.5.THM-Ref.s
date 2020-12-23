%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1091+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 137 expanded)
%              Number of leaves         :   17 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  234 ( 511 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2521,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2058,f2062,f2067,f2069,f2122,f2149,f2216,f2261,f2503,f2516])).

fof(f2516,plain,
    ( ~ spl56_5
    | spl56_23
    | ~ spl56_35 ),
    inference(avatar_contradiction_clause,[],[f2515])).

fof(f2515,plain,
    ( $false
    | ~ spl56_5
    | spl56_23
    | ~ spl56_35 ),
    inference(subsumption_resolution,[],[f2511,f2260])).

fof(f2260,plain,
    ( ~ v1_finset_1(sK54(sK0))
    | spl56_23 ),
    inference(avatar_component_clause,[],[f2259])).

fof(f2259,plain,
    ( spl56_23
  <=> v1_finset_1(sK54(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl56_23])])).

fof(f2511,plain,
    ( v1_finset_1(sK54(sK0))
    | ~ spl56_5
    | ~ spl56_35 ),
    inference(resolution,[],[f2502,f2065])).

fof(f2065,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK0)
        | v1_finset_1(X2) )
    | ~ spl56_5 ),
    inference(avatar_component_clause,[],[f2064])).

fof(f2064,plain,
    ( spl56_5
  <=> ! [X2] :
        ( v1_finset_1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl56_5])])).

fof(f2502,plain,
    ( r2_hidden(sK54(sK0),sK0)
    | ~ spl56_35 ),
    inference(avatar_component_clause,[],[f2501])).

fof(f2501,plain,
    ( spl56_35
  <=> r2_hidden(sK54(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl56_35])])).

fof(f2503,plain,
    ( spl56_35
    | ~ spl56_1
    | spl56_3 ),
    inference(avatar_split_clause,[],[f2499,f2056,f2050,f2501])).

fof(f2050,plain,
    ( spl56_1
  <=> v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl56_1])])).

fof(f2056,plain,
    ( spl56_3
  <=> v1_finset_1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl56_3])])).

fof(f2499,plain,
    ( r2_hidden(sK54(sK0),sK0)
    | ~ spl56_1
    | spl56_3 ),
    inference(subsumption_resolution,[],[f2490,f2068])).

fof(f2068,plain,
    ( v1_finset_1(sK0)
    | ~ spl56_1 ),
    inference(avatar_component_clause,[],[f2050])).

fof(f2490,plain,
    ( r2_hidden(sK54(sK0),sK0)
    | ~ v1_finset_1(sK0)
    | spl56_3 ),
    inference(resolution,[],[f2037,f2057])).

fof(f2057,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | spl56_3 ),
    inference(avatar_component_clause,[],[f2056])).

fof(f2037,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | r2_hidden(sK54(X0),X0)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f1905])).

fof(f1905,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK54(X0))
        & r2_hidden(sK54(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK54])],[f1781,f1904])).

fof(f1904,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK54(X0))
        & r2_hidden(sK54(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1781,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f1780])).

fof(f1780,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1725])).

fof(f1725,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(f2261,plain,
    ( ~ spl56_23
    | ~ spl56_1
    | spl56_3 ),
    inference(avatar_split_clause,[],[f2257,f2056,f2050,f2259])).

fof(f2257,plain,
    ( ~ v1_finset_1(sK54(sK0))
    | ~ spl56_1
    | spl56_3 ),
    inference(subsumption_resolution,[],[f2247,f2068])).

fof(f2247,plain,
    ( ~ v1_finset_1(sK54(sK0))
    | ~ v1_finset_1(sK0)
    | spl56_3 ),
    inference(resolution,[],[f2038,f2057])).

fof(f2038,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(sK54(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f1905])).

fof(f2216,plain,
    ( spl56_2
    | ~ spl56_3
    | ~ spl56_4 ),
    inference(avatar_contradiction_clause,[],[f2215])).

fof(f2215,plain,
    ( $false
    | spl56_2
    | ~ spl56_3
    | ~ spl56_4 ),
    inference(subsumption_resolution,[],[f2208,f2061])).

fof(f2061,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl56_4 ),
    inference(avatar_component_clause,[],[f2060])).

fof(f2060,plain,
    ( spl56_4
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl56_4])])).

fof(f2208,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl56_2
    | ~ spl56_3 ),
    inference(resolution,[],[f2157,f2066])).

fof(f2066,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ spl56_3 ),
    inference(avatar_component_clause,[],[f2056])).

fof(f2157,plain,
    ( ! [X0] :
        ( ~ v1_finset_1(k3_tarski(X0))
        | ~ r2_hidden(sK1,X0) )
    | spl56_2 ),
    inference(resolution,[],[f2150,f1932])).

fof(f1932,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1755])).

fof(f1755,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f441])).

fof(f441,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f2150,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v1_finset_1(X0) )
    | spl56_2 ),
    inference(resolution,[],[f2054,f2029])).

fof(f2029,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1770])).

fof(f1770,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1769])).

fof(f1769,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1731])).

fof(f1731,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(f2054,plain,
    ( ~ v1_finset_1(sK1)
    | spl56_2 ),
    inference(avatar_component_clause,[],[f2053])).

fof(f2053,plain,
    ( spl56_2
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl56_2])])).

fof(f2149,plain,
    ( ~ spl56_3
    | spl56_12 ),
    inference(avatar_contradiction_clause,[],[f2148])).

fof(f2148,plain,
    ( $false
    | ~ spl56_3
    | spl56_12 ),
    inference(subsumption_resolution,[],[f2145,f2066])).

fof(f2145,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | spl56_12 ),
    inference(resolution,[],[f2121,f2042])).

fof(f2042,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f1785])).

fof(f1785,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f1720])).

fof(f1720,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(f2121,plain,
    ( ~ v1_finset_1(k1_zfmisc_1(k3_tarski(sK0)))
    | spl56_12 ),
    inference(avatar_component_clause,[],[f2120])).

fof(f2120,plain,
    ( spl56_12
  <=> v1_finset_1(k1_zfmisc_1(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl56_12])])).

fof(f2122,plain,
    ( ~ spl56_12
    | spl56_1 ),
    inference(avatar_split_clause,[],[f2116,f2050,f2120])).

fof(f2116,plain,
    ( ~ v1_finset_1(k1_zfmisc_1(k3_tarski(sK0)))
    | spl56_1 ),
    inference(resolution,[],[f2114,f2014])).

fof(f2014,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f320])).

fof(f320,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f2114,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ v1_finset_1(X0) )
    | spl56_1 ),
    inference(resolution,[],[f2029,f2051])).

fof(f2051,plain,
    ( ~ v1_finset_1(sK0)
    | spl56_1 ),
    inference(avatar_component_clause,[],[f2050])).

fof(f2069,plain,
    ( spl56_1
    | spl56_3 ),
    inference(avatar_split_clause,[],[f1908,f2056,f2050])).

fof(f1908,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f1791])).

fof(f1791,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK0))
      | ( ~ v1_finset_1(sK1)
        & r2_hidden(sK1,sK0) )
      | ~ v1_finset_1(sK0) )
    & ( v1_finset_1(k3_tarski(sK0))
      | ( ! [X2] :
            ( v1_finset_1(X2)
            | ~ r2_hidden(X2,sK0) )
        & v1_finset_1(sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1788,f1790,f1789])).

fof(f1789,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ? [X1] :
              ( ~ v1_finset_1(X1)
              & r2_hidden(X1,X0) )
          | ~ v1_finset_1(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | ( ! [X2] :
                ( v1_finset_1(X2)
                | ~ r2_hidden(X2,X0) )
            & v1_finset_1(X0) ) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,sK0) )
        | ~ v1_finset_1(sK0) )
      & ( v1_finset_1(k3_tarski(sK0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,sK0) )
          & v1_finset_1(sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1790,plain,
    ( ? [X1] :
        ( ~ v1_finset_1(X1)
        & r2_hidden(X1,sK0) )
   => ( ~ v1_finset_1(sK1)
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1788,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(rectify,[],[f1787])).

fof(f1787,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(flattening,[],[f1786])).

fof(f1786,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(nnf_transformation,[],[f1744])).

fof(f1744,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f1739])).

fof(f1739,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f1738])).

fof(f1738,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(f2067,plain,
    ( spl56_5
    | spl56_3 ),
    inference(avatar_split_clause,[],[f1909,f2056,f2064])).

fof(f1909,plain,(
    ! [X2] :
      ( v1_finset_1(k3_tarski(sK0))
      | v1_finset_1(X2)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f1791])).

fof(f2062,plain,
    ( ~ spl56_1
    | spl56_4
    | ~ spl56_3 ),
    inference(avatar_split_clause,[],[f1910,f2056,f2060,f2050])).

fof(f1910,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | r2_hidden(sK1,sK0)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f1791])).

fof(f2058,plain,
    ( ~ spl56_1
    | ~ spl56_2
    | ~ spl56_3 ),
    inference(avatar_split_clause,[],[f1911,f2056,f2053,f2050])).

fof(f1911,plain,
    ( ~ v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK1)
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f1791])).
%------------------------------------------------------------------------------
