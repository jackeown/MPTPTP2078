%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:47 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  327 ( 703 expanded)
%              Number of leaves         :   69 ( 288 expanded)
%              Depth                    :   16
%              Number of atoms          : 1424 (3274 expanded)
%              Number of equality atoms :  233 ( 738 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2005,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f162,f167,f172,f177,f182,f187,f192,f197,f214,f226,f232,f259,f264,f318,f395,f425,f476,f485,f503,f568,f570,f622,f655,f688,f845,f854,f1637,f1680,f1710,f1749,f1867,f1885,f1897,f1935,f1981,f1998,f2002,f2003,f2004])).

fof(f2004,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2003,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK1 != k2_relat_1(sK2)
    | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2002,plain,
    ( sK2 != k2_funct_1(sK3)
    | sK0 != k1_relat_1(sK2)
    | sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1998,plain,
    ( ~ spl5_16
    | ~ spl5_18
    | spl5_68
    | ~ spl5_85 ),
    inference(avatar_contradiction_clause,[],[f1997])).

fof(f1997,plain,
    ( $false
    | ~ spl5_16
    | ~ spl5_18
    | spl5_68
    | ~ spl5_85 ),
    inference(subsumption_resolution,[],[f1996,f225])).

fof(f225,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl5_16
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1996,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_18
    | spl5_68
    | ~ spl5_85 ),
    inference(subsumption_resolution,[],[f1995,f258])).

fof(f258,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl5_18
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1995,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | spl5_68
    | ~ spl5_85 ),
    inference(subsumption_resolution,[],[f1992,f1748])).

fof(f1748,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl5_68 ),
    inference(avatar_component_clause,[],[f1746])).

fof(f1746,plain,
    ( spl5_68
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f1992,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl5_85 ),
    inference(resolution,[],[f1884,f251])).

fof(f251,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(X2))
      | k1_relat_1(X2) = X1
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f130,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1884,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3))
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f1882])).

fof(f1882,plain,
    ( spl5_85
  <=> r1_tarski(sK1,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f1981,plain,
    ( ~ spl5_9
    | ~ spl5_16
    | ~ spl5_38
    | spl5_79 ),
    inference(avatar_contradiction_clause,[],[f1980])).

fof(f1980,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_38
    | spl5_79 ),
    inference(subsumption_resolution,[],[f1979,f225])).

fof(f1979,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_9
    | ~ spl5_38
    | spl5_79 ),
    inference(subsumption_resolution,[],[f1978,f181])).

fof(f181,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1978,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_38
    | spl5_79 ),
    inference(subsumption_resolution,[],[f1976,f546])).

fof(f546,plain,
    ( v2_funct_1(sK3)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl5_38
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f1976,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl5_79 ),
    inference(resolution,[],[f1832,f97])).

fof(f97,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f1832,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl5_79 ),
    inference(avatar_component_clause,[],[f1830])).

fof(f1830,plain,
    ( spl5_79
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f1935,plain,
    ( ~ spl5_9
    | ~ spl5_16
    | spl5_77 ),
    inference(avatar_contradiction_clause,[],[f1934])).

fof(f1934,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_16
    | spl5_77 ),
    inference(subsumption_resolution,[],[f1933,f225])).

fof(f1933,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_9
    | spl5_77 ),
    inference(subsumption_resolution,[],[f1931,f181])).

fof(f1931,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl5_77 ),
    inference(resolution,[],[f1824,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1824,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl5_77 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f1822,plain,
    ( spl5_77
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f1897,plain,
    ( ~ spl5_77
    | ~ spl5_78
    | ~ spl5_79
    | spl5_86
    | ~ spl5_87
    | ~ spl5_72
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_37
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f1888,f565,f533,f223,f179,f1772,f1894,f1890,f1830,f1826,f1822])).

fof(f1826,plain,
    ( spl5_78
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f1890,plain,
    ( spl5_86
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f1894,plain,
    ( spl5_87
  <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f1772,plain,
    ( spl5_72
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f533,plain,
    ( spl5_37
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f565,plain,
    ( spl5_41
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1888,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_37
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f1887,f535])).

fof(f535,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f533])).

fof(f1887,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f1886,f225])).

fof(f1886,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl5_9
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f1869,f181])).

fof(f1869,plain,
    ( k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl5_41 ),
    inference(superposition,[],[f89,f567])).

fof(f567,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f565])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f1885,plain,
    ( spl5_85
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_38
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f1880,f565,f544,f223,f179,f1882])).

fof(f1880,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3))
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_38
    | ~ spl5_41 ),
    inference(forward_demodulation,[],[f1879,f118])).

fof(f118,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1879,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3))
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_38
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f1878,f181])).

fof(f1878,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl5_16
    | ~ spl5_38
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f1877,f546])).

fof(f1877,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl5_16
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f1876,f225])).

fof(f1876,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl5_41 ),
    inference(duplicate_literal_removal,[],[f1868])).

fof(f1868,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_41 ),
    inference(superposition,[],[f307,f567])).

fof(f307,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k2_funct_1(X0))),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f301,f93])).

fof(f301,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k2_funct_1(X0))),k1_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f123,f92])).

fof(f92,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1867,plain,
    ( ~ spl5_9
    | ~ spl5_16
    | spl5_78 ),
    inference(avatar_contradiction_clause,[],[f1866])).

fof(f1866,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_16
    | spl5_78 ),
    inference(subsumption_resolution,[],[f1865,f225])).

fof(f1865,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl5_9
    | spl5_78 ),
    inference(subsumption_resolution,[],[f1863,f181])).

fof(f1863,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl5_78 ),
    inference(resolution,[],[f1828,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1828,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl5_78 ),
    inference(avatar_component_clause,[],[f1826])).

fof(f1749,plain,
    ( ~ spl5_38
    | spl5_66
    | ~ spl5_68
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_22
    | ~ spl5_37
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f1744,f851,f533,f313,f229,f223,f194,f179,f1746,f1722,f544])).

fof(f1722,plain,
    ( spl5_66
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f194,plain,
    ( spl5_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f229,plain,
    ( spl5_17
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f313,plain,
    ( spl5_22
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f851,plain,
    ( spl5_54
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f1744,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_22
    | ~ spl5_37
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f1743,f315])).

fof(f315,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f313])).

fof(f1743,plain,
    ( sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_37
    | ~ spl5_54 ),
    inference(trivial_inequality_removal,[],[f1742])).

fof(f1742,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_37
    | ~ spl5_54 ),
    inference(forward_demodulation,[],[f1741,f535])).

fof(f1741,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_17
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f1740,f225])).

fof(f1740,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f1739,f181])).

fof(f1739,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f1738,f231])).

fof(f231,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f229])).

fof(f1738,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_12
    | ~ spl5_54 ),
    inference(subsumption_resolution,[],[f1641,f196])).

fof(f196,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f194])).

fof(f1641,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_54 ),
    inference(superposition,[],[f89,f853])).

fof(f853,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f851])).

fof(f1710,plain,
    ( spl5_38
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f1709,f842,f194,f189,f184,f179,f174,f169,f164,f149,f544])).

fof(f149,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f164,plain,
    ( spl5_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f169,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f174,plain,
    ( spl5_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f184,plain,
    ( spl5_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f189,plain,
    ( spl5_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f842,plain,
    ( spl5_52
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f1709,plain,
    ( v2_funct_1(sK3)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f1708,f181])).

fof(f1708,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f1707,f176])).

fof(f176,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f174])).

fof(f1707,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f1706,f171])).

fof(f171,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f169])).

fof(f1706,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f1699,f151])).

fof(f151,plain,
    ( k1_xboole_0 != sK0
    | spl5_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f1699,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f1690,f105])).

fof(f105,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1690,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_52 ),
    inference(superposition,[],[f520,f844])).

fof(f844,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f842])).

fof(f520,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f519,f196])).

fof(f519,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f518,f191])).

fof(f191,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f189])).

fof(f518,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f517,f186])).

fof(f186,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f517,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_6 ),
    inference(trivial_inequality_removal,[],[f514])).

fof(f514,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl5_6 ),
    inference(superposition,[],[f101,f166])).

fof(f166,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f164])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f1680,plain,
    ( ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | spl5_51 ),
    inference(avatar_contradiction_clause,[],[f1679])).

fof(f1679,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | spl5_51 ),
    inference(subsumption_resolution,[],[f1678,f196])).

fof(f1678,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | spl5_51 ),
    inference(subsumption_resolution,[],[f1677,f186])).

fof(f1677,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_7
    | ~ spl5_9
    | spl5_51 ),
    inference(subsumption_resolution,[],[f1676,f181])).

fof(f1676,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_7
    | spl5_51 ),
    inference(subsumption_resolution,[],[f1673,f171])).

fof(f1673,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_51 ),
    inference(resolution,[],[f840,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f840,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_51 ),
    inference(avatar_component_clause,[],[f838])).

fof(f838,plain,
    ( spl5_51
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f1637,plain,
    ( ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | spl5_53 ),
    inference(avatar_contradiction_clause,[],[f1635])).

fof(f1635,plain,
    ( $false
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | spl5_53 ),
    inference(unit_resulting_resolution,[],[f196,f181,f186,f171,f849,f401])).

fof(f401,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f400])).

fof(f400,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f112,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f849,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_53 ),
    inference(avatar_component_clause,[],[f847])).

fof(f847,plain,
    ( spl5_53
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f854,plain,
    ( ~ spl5_53
    | spl5_54
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f835,f392,f851,f847])).

fof(f392,plain,
    ( spl5_26
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f835,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_26 ),
    inference(resolution,[],[f321,f394])).

fof(f394,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f392])).

fof(f321,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f106,f217])).

fof(f217,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f109,f110])).

fof(f110,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f109,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f845,plain,
    ( ~ spl5_51
    | spl5_52
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f834,f211,f842,f838])).

fof(f211,plain,
    ( spl5_15
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f834,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_15 ),
    inference(resolution,[],[f321,f213])).

fof(f213,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f688,plain,
    ( spl5_47
    | ~ spl5_45
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f687,f629,f619,f633])).

fof(f633,plain,
    ( spl5_47
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f619,plain,
    ( spl5_45
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f629,plain,
    ( spl5_46
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f687,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_45
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f686,f621])).

fof(f621,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f619])).

fof(f686,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_46 ),
    inference(resolution,[],[f630,f130])).

fof(f630,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f629])).

fof(f655,plain,
    ( ~ spl5_17
    | ~ spl5_19
    | spl5_46 ),
    inference(avatar_contradiction_clause,[],[f654])).

fof(f654,plain,
    ( $false
    | ~ spl5_17
    | ~ spl5_19
    | spl5_46 ),
    inference(subsumption_resolution,[],[f653,f231])).

fof(f653,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_19
    | spl5_46 ),
    inference(subsumption_resolution,[],[f651,f263])).

fof(f263,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl5_19
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f651,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl5_46 ),
    inference(resolution,[],[f631,f124])).

fof(f631,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl5_46 ),
    inference(avatar_component_clause,[],[f629])).

fof(f622,plain,
    ( spl5_45
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f617,f473,f229,f194,f154,f619])).

fof(f154,plain,
    ( spl5_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f473,plain,
    ( spl5_35
  <=> r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f617,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f616,f231])).

fof(f616,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f615,f196])).

fof(f615,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f605,f156])).

fof(f156,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f605,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_35 ),
    inference(superposition,[],[f475,f92])).

fof(f475,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2)))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f473])).

fof(f570,plain,
    ( spl5_37
    | ~ spl5_7
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f569,f500,f169,f533])).

fof(f500,plain,
    ( spl5_36
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f569,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_7
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f526,f171])).

fof(f526,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_36 ),
    inference(superposition,[],[f114,f502])).

fof(f502,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f500])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f568,plain,
    ( spl5_41
    | ~ spl5_38
    | spl5_3
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f563,f500,f179,f174,f169,f149,f544,f565])).

fof(f563,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl5_3
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f562,f181])).

fof(f562,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl5_3
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f561,f176])).

fof(f561,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl5_3
    | ~ spl5_7
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f560,f171])).

fof(f560,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl5_3
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f527,f151])).

fof(f527,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_36 ),
    inference(trivial_inequality_removal,[],[f525])).

fof(f525,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_36 ),
    inference(superposition,[],[f403,f502])).

fof(f403,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f87,f110])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f503,plain,
    ( spl5_36
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f498,f211,f194,f189,f184,f179,f174,f169,f500])).

fof(f498,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f497,f181])).

fof(f497,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f496,f176])).

fof(f496,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_7
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f495,f171])).

fof(f495,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f494,f196])).

fof(f494,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f493,f191])).

fof(f493,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f490,f186])).

fof(f490,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_15 ),
    inference(resolution,[],[f489,f213])).

fof(f489,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f108,f110])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f485,plain,
    ( ~ spl5_12
    | ~ spl5_17
    | spl5_29 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_17
    | spl5_29 ),
    inference(subsumption_resolution,[],[f483,f231])).

fof(f483,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_12
    | spl5_29 ),
    inference(subsumption_resolution,[],[f481,f196])).

fof(f481,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_29 ),
    inference(resolution,[],[f448,f93])).

fof(f448,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl5_29
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f476,plain,
    ( ~ spl5_29
    | spl5_35
    | ~ spl5_17
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f471,f422,f229,f473,f446])).

fof(f422,plain,
    ( spl5_27
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f471,plain,
    ( r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_17
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f470,f118])).

fof(f470,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_17
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f441,f231])).

fof(f441,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_27 ),
    inference(superposition,[],[f123,f424])).

fof(f424,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f422])).

fof(f425,plain,
    ( spl5_27
    | spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f420,f194,f189,f184,f164,f154,f144,f422])).

fof(f144,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f420,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f419,f196])).

fof(f419,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f418,f191])).

fof(f418,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f417,f186])).

fof(f417,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f416,f156])).

fof(f416,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f415,f146])).

fof(f146,plain,
    ( k1_xboole_0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f415,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_6 ),
    inference(trivial_inequality_removal,[],[f412])).

fof(f412,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f403,f166])).

fof(f395,plain,
    ( spl5_26
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f390,f211,f194,f184,f179,f169,f392])).

fof(f390,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f389,f196])).

fof(f389,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f388,f186])).

fof(f388,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f387,f181])).

fof(f387,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f384,f171])).

fof(f384,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_15 ),
    inference(superposition,[],[f213,f113])).

fof(f318,plain,
    ( spl5_22
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f317,f184,f164,f313])).

fof(f317,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f310,f186])).

fof(f310,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_6 ),
    inference(superposition,[],[f166,f114])).

fof(f264,plain,
    ( spl5_19
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f253,f184,f261])).

fof(f253,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f131,f186])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f259,plain,
    ( spl5_18
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f252,f169,f256])).

fof(f252,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f131,f171])).

fof(f232,plain,
    ( spl5_17
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f227,f184,f229])).

fof(f227,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f219,f120])).

fof(f120,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f219,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_10 ),
    inference(resolution,[],[f119,f186])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f226,plain,
    ( spl5_16
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f221,f169,f223])).

fof(f221,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f218,f120])).

fof(f218,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f119,f171])).

fof(f214,plain,
    ( spl5_15
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f209,f159,f211])).

fof(f159,plain,
    ( spl5_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f209,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f161,f110])).

fof(f161,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f197,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f75,f194])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f67,f66])).

fof(f66,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f192,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f76,f189])).

fof(f76,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f187,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f77,f184])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

fof(f182,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f78,f179])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f177,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f79,f174])).

fof(f79,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f172,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f80,f169])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f68])).

fof(f167,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f81,f164])).

fof(f81,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f162,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f82,f159])).

fof(f82,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

fof(f157,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f83,f154])).

fof(f83,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f152,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f84,f149])).

fof(f84,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f68])).

fof(f147,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f85,f144])).

fof(f85,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f68])).

fof(f142,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f86,f139])).

fof(f139,plain,
    ( spl5_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f86,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:57:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (29873)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (29888)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (29880)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (29875)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (29871)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (29866)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (29867)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (29868)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (29891)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (29869)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (29883)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (29877)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (29894)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (29895)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (29889)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (29882)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.55  % (29892)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (29882)Refutation not found, incomplete strategy% (29882)------------------------------
% 1.39/0.55  % (29882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (29882)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (29882)Memory used [KB]: 10746
% 1.39/0.55  % (29882)Time elapsed: 0.139 s
% 1.39/0.55  % (29882)------------------------------
% 1.39/0.55  % (29882)------------------------------
% 1.39/0.55  % (29881)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.56  % (29886)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.56  % (29890)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.56  % (29872)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.56  % (29878)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.39/0.56  % (29876)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.56  % (29874)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.56  % (29884)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.53/0.57  % (29887)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.53/0.58  % (29870)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.53/0.58  % (29893)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.53/0.58  % (29885)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.53/0.58  % (29879)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.19/0.70  % (29896)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.19/0.71  % (29887)Refutation found. Thanks to Tanya!
% 2.19/0.71  % SZS status Theorem for theBenchmark
% 2.19/0.71  % SZS output start Proof for theBenchmark
% 2.19/0.71  fof(f2005,plain,(
% 2.19/0.71    $false),
% 2.19/0.71    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f162,f167,f172,f177,f182,f187,f192,f197,f214,f226,f232,f259,f264,f318,f395,f425,f476,f485,f503,f568,f570,f622,f655,f688,f845,f854,f1637,f1680,f1710,f1749,f1867,f1885,f1897,f1935,f1981,f1998,f2002,f2003,f2004])).
% 2.19/0.71  fof(f2004,plain,(
% 2.19/0.71    sK2 != k2_funct_1(sK3) | sK3 != k2_funct_1(k2_funct_1(sK3)) | k2_funct_1(sK2) = sK3),
% 2.19/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.19/0.71  fof(f2003,plain,(
% 2.19/0.71    sK2 != k2_funct_1(sK3) | sK1 != k2_relat_1(sK2) | k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 2.19/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.19/0.71  fof(f2002,plain,(
% 2.19/0.71    sK2 != k2_funct_1(sK3) | sK0 != k1_relat_1(sK2) | sK0 = k1_relat_1(k2_funct_1(sK3))),
% 2.19/0.71    introduced(theory_tautology_sat_conflict,[])).
% 2.19/0.71  fof(f1998,plain,(
% 2.19/0.71    ~spl5_16 | ~spl5_18 | spl5_68 | ~spl5_85),
% 2.19/0.71    inference(avatar_contradiction_clause,[],[f1997])).
% 2.19/0.71  fof(f1997,plain,(
% 2.19/0.71    $false | (~spl5_16 | ~spl5_18 | spl5_68 | ~spl5_85)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1996,f225])).
% 2.19/0.71  fof(f225,plain,(
% 2.19/0.71    v1_relat_1(sK3) | ~spl5_16),
% 2.19/0.71    inference(avatar_component_clause,[],[f223])).
% 2.19/0.71  fof(f223,plain,(
% 2.19/0.71    spl5_16 <=> v1_relat_1(sK3)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.19/0.71  fof(f1996,plain,(
% 2.19/0.71    ~v1_relat_1(sK3) | (~spl5_18 | spl5_68 | ~spl5_85)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1995,f258])).
% 2.19/0.71  fof(f258,plain,(
% 2.19/0.71    v4_relat_1(sK3,sK1) | ~spl5_18),
% 2.19/0.71    inference(avatar_component_clause,[],[f256])).
% 2.19/0.71  fof(f256,plain,(
% 2.19/0.71    spl5_18 <=> v4_relat_1(sK3,sK1)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.19/0.71  fof(f1995,plain,(
% 2.19/0.71    ~v4_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | (spl5_68 | ~spl5_85)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1992,f1748])).
% 2.19/0.71  fof(f1748,plain,(
% 2.19/0.71    sK1 != k1_relat_1(sK3) | spl5_68),
% 2.19/0.71    inference(avatar_component_clause,[],[f1746])).
% 2.19/0.71  fof(f1746,plain,(
% 2.19/0.71    spl5_68 <=> sK1 = k1_relat_1(sK3)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 2.19/0.71  fof(f1992,plain,(
% 2.19/0.71    sK1 = k1_relat_1(sK3) | ~v4_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | ~spl5_85),
% 2.19/0.71    inference(resolution,[],[f1884,f251])).
% 2.19/0.71  fof(f251,plain,(
% 2.19/0.71    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(X2)) | k1_relat_1(X2) = X1 | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 2.19/0.71    inference(resolution,[],[f130,f124])).
% 2.19/0.71  fof(f124,plain,(
% 2.19/0.71    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f70])).
% 2.19/0.71  fof(f70,plain,(
% 2.19/0.71    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.19/0.71    inference(nnf_transformation,[],[f64])).
% 2.19/0.71  fof(f64,plain,(
% 2.19/0.71    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.19/0.71    inference(ennf_transformation,[],[f6])).
% 2.19/0.71  fof(f6,axiom,(
% 2.19/0.71    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.19/0.71  fof(f130,plain,(
% 2.19/0.71    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f74])).
% 2.19/0.71  fof(f74,plain,(
% 2.19/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.71    inference(flattening,[],[f73])).
% 2.19/0.71  fof(f73,plain,(
% 2.19/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.71    inference(nnf_transformation,[],[f4])).
% 2.19/0.71  fof(f4,axiom,(
% 2.19/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.19/0.71  fof(f1884,plain,(
% 2.19/0.71    r1_tarski(sK1,k1_relat_1(sK3)) | ~spl5_85),
% 2.19/0.71    inference(avatar_component_clause,[],[f1882])).
% 2.19/0.71  fof(f1882,plain,(
% 2.19/0.71    spl5_85 <=> r1_tarski(sK1,k1_relat_1(sK3))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 2.19/0.71  fof(f1981,plain,(
% 2.19/0.71    ~spl5_9 | ~spl5_16 | ~spl5_38 | spl5_79),
% 2.19/0.71    inference(avatar_contradiction_clause,[],[f1980])).
% 2.19/0.71  fof(f1980,plain,(
% 2.19/0.71    $false | (~spl5_9 | ~spl5_16 | ~spl5_38 | spl5_79)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1979,f225])).
% 2.19/0.71  fof(f1979,plain,(
% 2.19/0.71    ~v1_relat_1(sK3) | (~spl5_9 | ~spl5_38 | spl5_79)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1978,f181])).
% 2.19/0.71  fof(f181,plain,(
% 2.19/0.71    v1_funct_1(sK3) | ~spl5_9),
% 2.19/0.71    inference(avatar_component_clause,[],[f179])).
% 2.19/0.71  fof(f179,plain,(
% 2.19/0.71    spl5_9 <=> v1_funct_1(sK3)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.19/0.71  fof(f1978,plain,(
% 2.19/0.71    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl5_38 | spl5_79)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1976,f546])).
% 2.19/0.71  fof(f546,plain,(
% 2.19/0.71    v2_funct_1(sK3) | ~spl5_38),
% 2.19/0.71    inference(avatar_component_clause,[],[f544])).
% 2.19/0.71  fof(f544,plain,(
% 2.19/0.71    spl5_38 <=> v2_funct_1(sK3)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.19/0.71  fof(f1976,plain,(
% 2.19/0.71    ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl5_79),
% 2.19/0.71    inference(resolution,[],[f1832,f97])).
% 2.19/0.71  fof(f97,plain,(
% 2.19/0.71    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f47])).
% 2.19/0.71  fof(f47,plain,(
% 2.19/0.71    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/0.71    inference(flattening,[],[f46])).
% 2.19/0.71  fof(f46,plain,(
% 2.19/0.71    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.19/0.71    inference(ennf_transformation,[],[f15])).
% 2.19/0.71  fof(f15,axiom,(
% 2.19/0.71    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 2.19/0.71  fof(f1832,plain,(
% 2.19/0.71    ~v2_funct_1(k2_funct_1(sK3)) | spl5_79),
% 2.19/0.71    inference(avatar_component_clause,[],[f1830])).
% 2.19/0.71  fof(f1830,plain,(
% 2.19/0.71    spl5_79 <=> v2_funct_1(k2_funct_1(sK3))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 2.19/0.71  fof(f1935,plain,(
% 2.19/0.71    ~spl5_9 | ~spl5_16 | spl5_77),
% 2.19/0.71    inference(avatar_contradiction_clause,[],[f1934])).
% 2.19/0.71  fof(f1934,plain,(
% 2.19/0.71    $false | (~spl5_9 | ~spl5_16 | spl5_77)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1933,f225])).
% 2.19/0.71  fof(f1933,plain,(
% 2.19/0.71    ~v1_relat_1(sK3) | (~spl5_9 | spl5_77)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1931,f181])).
% 2.19/0.71  fof(f1931,plain,(
% 2.19/0.71    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl5_77),
% 2.19/0.71    inference(resolution,[],[f1824,f93])).
% 2.19/0.71  fof(f93,plain,(
% 2.19/0.71    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f45])).
% 2.19/0.71  fof(f45,plain,(
% 2.19/0.71    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/0.71    inference(flattening,[],[f44])).
% 2.19/0.71  fof(f44,plain,(
% 2.19/0.71    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.19/0.71    inference(ennf_transformation,[],[f12])).
% 2.19/0.71  fof(f12,axiom,(
% 2.19/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.19/0.71  fof(f1824,plain,(
% 2.19/0.71    ~v1_relat_1(k2_funct_1(sK3)) | spl5_77),
% 2.19/0.71    inference(avatar_component_clause,[],[f1822])).
% 2.19/0.71  fof(f1822,plain,(
% 2.19/0.71    spl5_77 <=> v1_relat_1(k2_funct_1(sK3))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 2.19/0.71  fof(f1897,plain,(
% 2.19/0.71    ~spl5_77 | ~spl5_78 | ~spl5_79 | spl5_86 | ~spl5_87 | ~spl5_72 | ~spl5_9 | ~spl5_16 | ~spl5_37 | ~spl5_41),
% 2.19/0.71    inference(avatar_split_clause,[],[f1888,f565,f533,f223,f179,f1772,f1894,f1890,f1830,f1826,f1822])).
% 2.19/0.71  fof(f1826,plain,(
% 2.19/0.71    spl5_78 <=> v1_funct_1(k2_funct_1(sK3))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 2.19/0.71  fof(f1890,plain,(
% 2.19/0.71    spl5_86 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).
% 2.19/0.71  fof(f1894,plain,(
% 2.19/0.71    spl5_87 <=> k6_relat_1(sK1) = k6_relat_1(k2_relat_1(k2_funct_1(sK3)))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 2.19/0.71  fof(f1772,plain,(
% 2.19/0.71    spl5_72 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 2.19/0.71  fof(f533,plain,(
% 2.19/0.71    spl5_37 <=> sK0 = k2_relat_1(sK3)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.19/0.71  fof(f565,plain,(
% 2.19/0.71    spl5_41 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 2.19/0.71  fof(f1888,plain,(
% 2.19/0.71    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl5_9 | ~spl5_16 | ~spl5_37 | ~spl5_41)),
% 2.19/0.71    inference(forward_demodulation,[],[f1887,f535])).
% 2.19/0.71  fof(f535,plain,(
% 2.19/0.71    sK0 = k2_relat_1(sK3) | ~spl5_37),
% 2.19/0.71    inference(avatar_component_clause,[],[f533])).
% 2.19/0.71  fof(f1887,plain,(
% 2.19/0.71    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl5_9 | ~spl5_16 | ~spl5_41)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1886,f225])).
% 2.19/0.71  fof(f1886,plain,(
% 2.19/0.71    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl5_9 | ~spl5_41)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1869,f181])).
% 2.19/0.71  fof(f1869,plain,(
% 2.19/0.71    k6_relat_1(sK1) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl5_41),
% 2.19/0.71    inference(superposition,[],[f89,f567])).
% 2.19/0.71  fof(f567,plain,(
% 2.19/0.71    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl5_41),
% 2.19/0.71    inference(avatar_component_clause,[],[f565])).
% 2.19/0.71  fof(f89,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f39])).
% 2.19/0.71  fof(f39,plain,(
% 2.19/0.71    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/0.71    inference(flattening,[],[f38])).
% 2.19/0.71  fof(f38,plain,(
% 2.19/0.71    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.19/0.71    inference(ennf_transformation,[],[f17])).
% 2.19/0.71  fof(f17,axiom,(
% 2.19/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 2.19/0.71  fof(f1885,plain,(
% 2.19/0.71    spl5_85 | ~spl5_9 | ~spl5_16 | ~spl5_38 | ~spl5_41),
% 2.19/0.71    inference(avatar_split_clause,[],[f1880,f565,f544,f223,f179,f1882])).
% 2.19/0.71  fof(f1880,plain,(
% 2.19/0.71    r1_tarski(sK1,k1_relat_1(sK3)) | (~spl5_9 | ~spl5_16 | ~spl5_38 | ~spl5_41)),
% 2.19/0.71    inference(forward_demodulation,[],[f1879,f118])).
% 2.19/0.71  fof(f118,plain,(
% 2.19/0.71    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.19/0.71    inference(cnf_transformation,[],[f9])).
% 2.19/0.71  fof(f9,axiom,(
% 2.19/0.71    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.19/0.71  fof(f1879,plain,(
% 2.19/0.71    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3)) | (~spl5_9 | ~spl5_16 | ~spl5_38 | ~spl5_41)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1878,f181])).
% 2.19/0.71  fof(f1878,plain,(
% 2.19/0.71    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | (~spl5_16 | ~spl5_38 | ~spl5_41)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1877,f546])).
% 2.19/0.71  fof(f1877,plain,(
% 2.19/0.71    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | (~spl5_16 | ~spl5_41)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1876,f225])).
% 2.19/0.71  fof(f1876,plain,(
% 2.19/0.71    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~spl5_41),
% 2.19/0.71    inference(duplicate_literal_removal,[],[f1868])).
% 2.19/0.71  fof(f1868,plain,(
% 2.19/0.71    r1_tarski(k2_relat_1(k6_relat_1(sK1)),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl5_41),
% 2.19/0.71    inference(superposition,[],[f307,f567])).
% 2.19/0.71  fof(f307,plain,(
% 2.19/0.71    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k2_funct_1(X0))),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.71    inference(subsumption_resolution,[],[f301,f93])).
% 2.19/0.71  fof(f301,plain,(
% 2.19/0.71    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k2_funct_1(X0))),k1_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.71    inference(superposition,[],[f123,f92])).
% 2.19/0.71  fof(f92,plain,(
% 2.19/0.71    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f43])).
% 2.19/0.71  fof(f43,plain,(
% 2.19/0.71    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/0.71    inference(flattening,[],[f42])).
% 2.19/0.71  fof(f42,plain,(
% 2.19/0.71    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.19/0.71    inference(ennf_transformation,[],[f16])).
% 2.19/0.71  fof(f16,axiom,(
% 2.19/0.71    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.19/0.71  fof(f123,plain,(
% 2.19/0.71    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f63])).
% 2.19/0.71  fof(f63,plain,(
% 2.19/0.71    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.19/0.71    inference(ennf_transformation,[],[f8])).
% 2.19/0.71  fof(f8,axiom,(
% 2.19/0.71    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 2.19/0.71  fof(f1867,plain,(
% 2.19/0.71    ~spl5_9 | ~spl5_16 | spl5_78),
% 2.19/0.71    inference(avatar_contradiction_clause,[],[f1866])).
% 2.19/0.71  fof(f1866,plain,(
% 2.19/0.71    $false | (~spl5_9 | ~spl5_16 | spl5_78)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1865,f225])).
% 2.19/0.71  fof(f1865,plain,(
% 2.19/0.71    ~v1_relat_1(sK3) | (~spl5_9 | spl5_78)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1863,f181])).
% 2.19/0.71  fof(f1863,plain,(
% 2.19/0.71    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl5_78),
% 2.19/0.71    inference(resolution,[],[f1828,f94])).
% 2.19/0.71  fof(f94,plain,(
% 2.19/0.71    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f45])).
% 2.19/0.71  fof(f1828,plain,(
% 2.19/0.71    ~v1_funct_1(k2_funct_1(sK3)) | spl5_78),
% 2.19/0.71    inference(avatar_component_clause,[],[f1826])).
% 2.19/0.71  fof(f1749,plain,(
% 2.19/0.71    ~spl5_38 | spl5_66 | ~spl5_68 | ~spl5_9 | ~spl5_12 | ~spl5_16 | ~spl5_17 | ~spl5_22 | ~spl5_37 | ~spl5_54),
% 2.19/0.71    inference(avatar_split_clause,[],[f1744,f851,f533,f313,f229,f223,f194,f179,f1746,f1722,f544])).
% 2.19/0.71  fof(f1722,plain,(
% 2.19/0.71    spl5_66 <=> sK2 = k2_funct_1(sK3)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 2.19/0.71  fof(f194,plain,(
% 2.19/0.71    spl5_12 <=> v1_funct_1(sK2)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.19/0.71  fof(f229,plain,(
% 2.19/0.71    spl5_17 <=> v1_relat_1(sK2)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.19/0.71  fof(f313,plain,(
% 2.19/0.71    spl5_22 <=> sK1 = k2_relat_1(sK2)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.19/0.71  fof(f851,plain,(
% 2.19/0.71    spl5_54 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 2.19/0.71  fof(f1744,plain,(
% 2.19/0.71    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | (~spl5_9 | ~spl5_12 | ~spl5_16 | ~spl5_17 | ~spl5_22 | ~spl5_37 | ~spl5_54)),
% 2.19/0.71    inference(forward_demodulation,[],[f1743,f315])).
% 2.19/0.71  fof(f315,plain,(
% 2.19/0.71    sK1 = k2_relat_1(sK2) | ~spl5_22),
% 2.19/0.71    inference(avatar_component_clause,[],[f313])).
% 2.19/0.71  fof(f1743,plain,(
% 2.19/0.71    sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | (~spl5_9 | ~spl5_12 | ~spl5_16 | ~spl5_17 | ~spl5_37 | ~spl5_54)),
% 2.19/0.71    inference(trivial_inequality_removal,[],[f1742])).
% 2.19/0.71  fof(f1742,plain,(
% 2.19/0.71    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | (~spl5_9 | ~spl5_12 | ~spl5_16 | ~spl5_17 | ~spl5_37 | ~spl5_54)),
% 2.19/0.71    inference(forward_demodulation,[],[f1741,f535])).
% 2.19/0.71  fof(f1741,plain,(
% 2.19/0.71    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | (~spl5_9 | ~spl5_12 | ~spl5_16 | ~spl5_17 | ~spl5_54)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1740,f225])).
% 2.19/0.71  fof(f1740,plain,(
% 2.19/0.71    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl5_9 | ~spl5_12 | ~spl5_17 | ~spl5_54)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1739,f181])).
% 2.19/0.71  fof(f1739,plain,(
% 2.19/0.71    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl5_12 | ~spl5_17 | ~spl5_54)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1738,f231])).
% 2.19/0.71  fof(f231,plain,(
% 2.19/0.71    v1_relat_1(sK2) | ~spl5_17),
% 2.19/0.71    inference(avatar_component_clause,[],[f229])).
% 2.19/0.71  fof(f1738,plain,(
% 2.19/0.71    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl5_12 | ~spl5_54)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1641,f196])).
% 2.19/0.71  fof(f196,plain,(
% 2.19/0.71    v1_funct_1(sK2) | ~spl5_12),
% 2.19/0.71    inference(avatar_component_clause,[],[f194])).
% 2.19/0.71  fof(f1641,plain,(
% 2.19/0.71    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl5_54),
% 2.19/0.71    inference(superposition,[],[f89,f853])).
% 2.19/0.71  fof(f853,plain,(
% 2.19/0.71    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl5_54),
% 2.19/0.71    inference(avatar_component_clause,[],[f851])).
% 2.19/0.71  fof(f1710,plain,(
% 2.19/0.71    spl5_38 | spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_52),
% 2.19/0.71    inference(avatar_split_clause,[],[f1709,f842,f194,f189,f184,f179,f174,f169,f164,f149,f544])).
% 2.19/0.71  fof(f149,plain,(
% 2.19/0.71    spl5_3 <=> k1_xboole_0 = sK0),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.19/0.71  fof(f164,plain,(
% 2.19/0.71    spl5_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.19/0.71  fof(f169,plain,(
% 2.19/0.71    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.19/0.71  fof(f174,plain,(
% 2.19/0.71    spl5_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.19/0.71  fof(f184,plain,(
% 2.19/0.71    spl5_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.19/0.71  fof(f189,plain,(
% 2.19/0.71    spl5_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.19/0.71  fof(f842,plain,(
% 2.19/0.71    spl5_52 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 2.19/0.71  fof(f1709,plain,(
% 2.19/0.71    v2_funct_1(sK3) | (spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_52)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1708,f181])).
% 2.19/0.71  fof(f1708,plain,(
% 2.19/0.71    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_52)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1707,f176])).
% 2.19/0.71  fof(f176,plain,(
% 2.19/0.71    v1_funct_2(sK3,sK1,sK0) | ~spl5_8),
% 2.19/0.71    inference(avatar_component_clause,[],[f174])).
% 2.19/0.71  fof(f1707,plain,(
% 2.19/0.71    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl5_3 | ~spl5_6 | ~spl5_7 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_52)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1706,f171])).
% 2.19/0.71  fof(f171,plain,(
% 2.19/0.71    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_7),
% 2.19/0.71    inference(avatar_component_clause,[],[f169])).
% 2.19/0.71  fof(f1706,plain,(
% 2.19/0.71    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl5_3 | ~spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_52)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1699,f151])).
% 2.19/0.71  fof(f151,plain,(
% 2.19/0.71    k1_xboole_0 != sK0 | spl5_3),
% 2.19/0.71    inference(avatar_component_clause,[],[f149])).
% 2.19/0.71  fof(f1699,plain,(
% 2.19/0.71    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_52)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1690,f105])).
% 2.19/0.71  fof(f105,plain,(
% 2.19/0.71    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.19/0.71    inference(cnf_transformation,[],[f14])).
% 2.19/0.71  fof(f14,axiom,(
% 2.19/0.71    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.19/0.71  fof(f1690,plain,(
% 2.19/0.71    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_52)),
% 2.19/0.71    inference(superposition,[],[f520,f844])).
% 2.19/0.71  fof(f844,plain,(
% 2.19/0.71    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl5_52),
% 2.19/0.71    inference(avatar_component_clause,[],[f842])).
% 2.19/0.71  fof(f520,plain,(
% 2.19/0.71    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 2.19/0.71    inference(subsumption_resolution,[],[f519,f196])).
% 2.19/0.71  fof(f519,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl5_6 | ~spl5_10 | ~spl5_11)),
% 2.19/0.71    inference(subsumption_resolution,[],[f518,f191])).
% 2.19/0.71  fof(f191,plain,(
% 2.19/0.71    v1_funct_2(sK2,sK0,sK1) | ~spl5_11),
% 2.19/0.71    inference(avatar_component_clause,[],[f189])).
% 2.19/0.71  fof(f518,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl5_6 | ~spl5_10)),
% 2.19/0.71    inference(subsumption_resolution,[],[f517,f186])).
% 2.19/0.71  fof(f186,plain,(
% 2.19/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_10),
% 2.19/0.71    inference(avatar_component_clause,[],[f184])).
% 2.19/0.71  fof(f517,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl5_6),
% 2.19/0.71    inference(trivial_inequality_removal,[],[f514])).
% 2.19/0.71  fof(f514,plain,(
% 2.19/0.71    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl5_6),
% 2.19/0.71    inference(superposition,[],[f101,f166])).
% 2.19/0.71  fof(f166,plain,(
% 2.19/0.71    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl5_6),
% 2.19/0.71    inference(avatar_component_clause,[],[f164])).
% 2.19/0.71  fof(f101,plain,(
% 2.19/0.71    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f49])).
% 2.19/0.71  fof(f49,plain,(
% 2.19/0.71    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.19/0.71    inference(flattening,[],[f48])).
% 2.19/0.71  fof(f48,plain,(
% 2.19/0.71    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.19/0.71    inference(ennf_transformation,[],[f28])).
% 2.19/0.71  fof(f28,axiom,(
% 2.19/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.19/0.71  fof(f1680,plain,(
% 2.19/0.71    ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_12 | spl5_51),
% 2.19/0.71    inference(avatar_contradiction_clause,[],[f1679])).
% 2.19/0.71  fof(f1679,plain,(
% 2.19/0.71    $false | (~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_12 | spl5_51)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1678,f196])).
% 2.19/0.71  fof(f1678,plain,(
% 2.19/0.71    ~v1_funct_1(sK2) | (~spl5_7 | ~spl5_9 | ~spl5_10 | spl5_51)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1677,f186])).
% 2.19/0.71  fof(f1677,plain,(
% 2.19/0.71    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_7 | ~spl5_9 | spl5_51)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1676,f181])).
% 2.19/0.71  fof(f1676,plain,(
% 2.19/0.71    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_7 | spl5_51)),
% 2.19/0.71    inference(subsumption_resolution,[],[f1673,f171])).
% 2.19/0.71  fof(f1673,plain,(
% 2.19/0.71    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl5_51),
% 2.19/0.71    inference(resolution,[],[f840,f112])).
% 2.19/0.71  fof(f112,plain,(
% 2.19/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f56])).
% 2.19/0.71  fof(f56,plain,(
% 2.19/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.19/0.71    inference(flattening,[],[f55])).
% 2.19/0.71  fof(f55,plain,(
% 2.19/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.19/0.71    inference(ennf_transformation,[],[f23])).
% 2.19/0.71  fof(f23,axiom,(
% 2.19/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.19/0.71  fof(f840,plain,(
% 2.19/0.71    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_51),
% 2.19/0.71    inference(avatar_component_clause,[],[f838])).
% 2.19/0.71  fof(f838,plain,(
% 2.19/0.71    spl5_51 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 2.19/0.71  fof(f1637,plain,(
% 2.19/0.71    ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_12 | spl5_53),
% 2.19/0.71    inference(avatar_contradiction_clause,[],[f1635])).
% 2.19/0.71  fof(f1635,plain,(
% 2.19/0.71    $false | (~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_12 | spl5_53)),
% 2.19/0.71    inference(unit_resulting_resolution,[],[f196,f181,f186,f171,f849,f401])).
% 2.19/0.71  fof(f401,plain,(
% 2.19/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.19/0.71    inference(duplicate_literal_removal,[],[f400])).
% 2.19/0.71  fof(f400,plain,(
% 2.19/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.19/0.71    inference(superposition,[],[f112,f113])).
% 2.19/0.71  fof(f113,plain,(
% 2.19/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f58])).
% 2.19/0.71  fof(f58,plain,(
% 2.19/0.71    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.19/0.71    inference(flattening,[],[f57])).
% 2.19/0.71  fof(f57,plain,(
% 2.19/0.71    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.19/0.71    inference(ennf_transformation,[],[f25])).
% 2.19/0.71  fof(f25,axiom,(
% 2.19/0.71    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.19/0.71  fof(f849,plain,(
% 2.19/0.71    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_53),
% 2.19/0.71    inference(avatar_component_clause,[],[f847])).
% 2.19/0.71  fof(f847,plain,(
% 2.19/0.71    spl5_53 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 2.19/0.71  fof(f854,plain,(
% 2.19/0.71    ~spl5_53 | spl5_54 | ~spl5_26),
% 2.19/0.71    inference(avatar_split_clause,[],[f835,f392,f851,f847])).
% 2.19/0.71  fof(f392,plain,(
% 2.19/0.71    spl5_26 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.19/0.71  fof(f835,plain,(
% 2.19/0.71    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_26),
% 2.19/0.71    inference(resolution,[],[f321,f394])).
% 2.19/0.71  fof(f394,plain,(
% 2.19/0.71    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl5_26),
% 2.19/0.71    inference(avatar_component_clause,[],[f392])).
% 2.19/0.71  fof(f321,plain,(
% 2.19/0.71    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.19/0.71    inference(resolution,[],[f106,f217])).
% 2.19/0.71  fof(f217,plain,(
% 2.19/0.71    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.19/0.71    inference(forward_demodulation,[],[f109,f110])).
% 2.19/0.71  fof(f110,plain,(
% 2.19/0.71    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f26])).
% 2.19/0.71  fof(f26,axiom,(
% 2.19/0.71    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.19/0.71  fof(f109,plain,(
% 2.19/0.71    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.19/0.71    inference(cnf_transformation,[],[f32])).
% 2.19/0.71  fof(f32,plain,(
% 2.19/0.71    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.19/0.71    inference(pure_predicate_removal,[],[f24])).
% 2.19/0.71  fof(f24,axiom,(
% 2.19/0.71    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.19/0.71  fof(f106,plain,(
% 2.19/0.71    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/0.71    inference(cnf_transformation,[],[f69])).
% 2.19/0.71  fof(f69,plain,(
% 2.19/0.71    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.71    inference(nnf_transformation,[],[f52])).
% 2.19/0.71  fof(f52,plain,(
% 2.19/0.71    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.71    inference(flattening,[],[f51])).
% 2.19/0.71  fof(f51,plain,(
% 2.19/0.71    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.19/0.71    inference(ennf_transformation,[],[f22])).
% 2.19/0.71  fof(f22,axiom,(
% 2.19/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.19/0.71  fof(f845,plain,(
% 2.19/0.71    ~spl5_51 | spl5_52 | ~spl5_15),
% 2.19/0.71    inference(avatar_split_clause,[],[f834,f211,f842,f838])).
% 2.19/0.71  fof(f211,plain,(
% 2.19/0.71    spl5_15 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.19/0.71  fof(f834,plain,(
% 2.19/0.71    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_15),
% 2.19/0.71    inference(resolution,[],[f321,f213])).
% 2.19/0.71  fof(f213,plain,(
% 2.19/0.71    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl5_15),
% 2.19/0.71    inference(avatar_component_clause,[],[f211])).
% 2.19/0.71  fof(f688,plain,(
% 2.19/0.71    spl5_47 | ~spl5_45 | ~spl5_46),
% 2.19/0.71    inference(avatar_split_clause,[],[f687,f629,f619,f633])).
% 2.19/0.71  fof(f633,plain,(
% 2.19/0.71    spl5_47 <=> sK0 = k1_relat_1(sK2)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 2.19/0.71  fof(f619,plain,(
% 2.19/0.71    spl5_45 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 2.19/0.71  fof(f629,plain,(
% 2.19/0.71    spl5_46 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 2.19/0.71  fof(f687,plain,(
% 2.19/0.71    sK0 = k1_relat_1(sK2) | (~spl5_45 | ~spl5_46)),
% 2.19/0.71    inference(subsumption_resolution,[],[f686,f621])).
% 2.19/0.71  fof(f621,plain,(
% 2.19/0.71    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl5_45),
% 2.19/0.71    inference(avatar_component_clause,[],[f619])).
% 2.19/0.71  fof(f686,plain,(
% 2.19/0.71    sK0 = k1_relat_1(sK2) | ~r1_tarski(sK0,k1_relat_1(sK2)) | ~spl5_46),
% 2.19/0.71    inference(resolution,[],[f630,f130])).
% 2.19/0.71  fof(f630,plain,(
% 2.19/0.71    r1_tarski(k1_relat_1(sK2),sK0) | ~spl5_46),
% 2.19/0.71    inference(avatar_component_clause,[],[f629])).
% 2.19/0.71  fof(f655,plain,(
% 2.19/0.71    ~spl5_17 | ~spl5_19 | spl5_46),
% 2.19/0.71    inference(avatar_contradiction_clause,[],[f654])).
% 2.19/0.71  fof(f654,plain,(
% 2.19/0.71    $false | (~spl5_17 | ~spl5_19 | spl5_46)),
% 2.19/0.71    inference(subsumption_resolution,[],[f653,f231])).
% 2.19/0.71  fof(f653,plain,(
% 2.19/0.71    ~v1_relat_1(sK2) | (~spl5_19 | spl5_46)),
% 2.19/0.71    inference(subsumption_resolution,[],[f651,f263])).
% 2.19/0.71  fof(f263,plain,(
% 2.19/0.71    v4_relat_1(sK2,sK0) | ~spl5_19),
% 2.19/0.71    inference(avatar_component_clause,[],[f261])).
% 2.19/0.71  fof(f261,plain,(
% 2.19/0.71    spl5_19 <=> v4_relat_1(sK2,sK0)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.19/0.71  fof(f651,plain,(
% 2.19/0.71    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl5_46),
% 2.19/0.71    inference(resolution,[],[f631,f124])).
% 2.19/0.71  fof(f631,plain,(
% 2.19/0.71    ~r1_tarski(k1_relat_1(sK2),sK0) | spl5_46),
% 2.19/0.71    inference(avatar_component_clause,[],[f629])).
% 2.19/0.71  fof(f622,plain,(
% 2.19/0.71    spl5_45 | ~spl5_4 | ~spl5_12 | ~spl5_17 | ~spl5_35),
% 2.19/0.71    inference(avatar_split_clause,[],[f617,f473,f229,f194,f154,f619])).
% 2.19/0.71  fof(f154,plain,(
% 2.19/0.71    spl5_4 <=> v2_funct_1(sK2)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.19/0.71  fof(f473,plain,(
% 2.19/0.71    spl5_35 <=> r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2)))),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 2.19/0.71  fof(f617,plain,(
% 2.19/0.71    r1_tarski(sK0,k1_relat_1(sK2)) | (~spl5_4 | ~spl5_12 | ~spl5_17 | ~spl5_35)),
% 2.19/0.71    inference(subsumption_resolution,[],[f616,f231])).
% 2.19/0.71  fof(f616,plain,(
% 2.19/0.71    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl5_4 | ~spl5_12 | ~spl5_35)),
% 2.19/0.71    inference(subsumption_resolution,[],[f615,f196])).
% 2.19/0.71  fof(f615,plain,(
% 2.19/0.71    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_4 | ~spl5_35)),
% 2.19/0.71    inference(subsumption_resolution,[],[f605,f156])).
% 2.19/0.71  fof(f156,plain,(
% 2.19/0.71    v2_funct_1(sK2) | ~spl5_4),
% 2.19/0.71    inference(avatar_component_clause,[],[f154])).
% 2.19/0.71  fof(f605,plain,(
% 2.19/0.71    r1_tarski(sK0,k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_35),
% 2.19/0.71    inference(superposition,[],[f475,f92])).
% 2.19/0.71  fof(f475,plain,(
% 2.19/0.71    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) | ~spl5_35),
% 2.19/0.71    inference(avatar_component_clause,[],[f473])).
% 2.19/0.71  fof(f570,plain,(
% 2.19/0.71    spl5_37 | ~spl5_7 | ~spl5_36),
% 2.19/0.71    inference(avatar_split_clause,[],[f569,f500,f169,f533])).
% 2.19/0.71  fof(f500,plain,(
% 2.19/0.71    spl5_36 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.19/0.71    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 2.19/0.71  fof(f569,plain,(
% 2.19/0.71    sK0 = k2_relat_1(sK3) | (~spl5_7 | ~spl5_36)),
% 2.19/0.71    inference(subsumption_resolution,[],[f526,f171])).
% 2.19/0.71  fof(f526,plain,(
% 2.19/0.71    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_36),
% 2.19/0.71    inference(superposition,[],[f114,f502])).
% 2.19/0.71  fof(f502,plain,(
% 2.19/0.71    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl5_36),
% 2.19/0.71    inference(avatar_component_clause,[],[f500])).
% 2.19/0.71  fof(f114,plain,(
% 2.19/0.71    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.19/0.71    inference(cnf_transformation,[],[f59])).
% 2.19/0.71  fof(f59,plain,(
% 2.19/0.71    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.19/0.71    inference(ennf_transformation,[],[f21])).
% 2.19/0.71  fof(f21,axiom,(
% 2.19/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.19/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.19/0.71  fof(f568,plain,(
% 2.19/0.71    spl5_41 | ~spl5_38 | spl5_3 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_36),
% 2.19/0.71    inference(avatar_split_clause,[],[f563,f500,f179,f174,f169,f149,f544,f565])).
% 2.19/0.71  fof(f563,plain,(
% 2.19/0.71    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl5_3 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_36)),
% 2.19/0.71    inference(subsumption_resolution,[],[f562,f181])).
% 2.19/0.71  fof(f562,plain,(
% 2.19/0.71    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl5_3 | ~spl5_7 | ~spl5_8 | ~spl5_36)),
% 2.19/0.71    inference(subsumption_resolution,[],[f561,f176])).
% 2.19/0.71  fof(f561,plain,(
% 2.19/0.71    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl5_3 | ~spl5_7 | ~spl5_36)),
% 2.19/0.71    inference(subsumption_resolution,[],[f560,f171])).
% 2.19/0.71  fof(f560,plain,(
% 2.19/0.71    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl5_3 | ~spl5_36)),
% 2.19/0.71    inference(subsumption_resolution,[],[f527,f151])).
% 2.19/0.71  fof(f527,plain,(
% 2.19/0.71    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl5_36),
% 2.19/0.71    inference(trivial_inequality_removal,[],[f525])).
% 2.19/0.71  fof(f525,plain,(
% 2.19/0.71    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl5_36),
% 2.19/0.71    inference(superposition,[],[f403,f502])).
% 2.19/0.71  fof(f403,plain,(
% 2.19/0.71    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.71    inference(forward_demodulation,[],[f87,f110])).
% 2.19/0.71  fof(f87,plain,(
% 2.19/0.71    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f37])).
% 2.19/0.71  fof(f37,plain,(
% 2.19/0.71    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/0.71    inference(flattening,[],[f36])).
% 2.19/0.71  fof(f36,plain,(
% 2.19/0.71    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.19/0.71    inference(ennf_transformation,[],[f29])).
% 2.19/0.73  fof(f29,axiom,(
% 2.19/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.19/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.19/0.73  fof(f503,plain,(
% 2.19/0.73    spl5_36 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_15),
% 2.19/0.73    inference(avatar_split_clause,[],[f498,f211,f194,f189,f184,f179,f174,f169,f500])).
% 2.19/0.73  fof(f498,plain,(
% 2.19/0.73    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_15)),
% 2.19/0.73    inference(subsumption_resolution,[],[f497,f181])).
% 2.19/0.73  fof(f497,plain,(
% 2.19/0.73    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_15)),
% 2.19/0.73    inference(subsumption_resolution,[],[f496,f176])).
% 2.19/0.73  fof(f496,plain,(
% 2.19/0.73    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl5_7 | ~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_15)),
% 2.19/0.73    inference(subsumption_resolution,[],[f495,f171])).
% 2.19/0.73  fof(f495,plain,(
% 2.19/0.73    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl5_10 | ~spl5_11 | ~spl5_12 | ~spl5_15)),
% 2.19/0.73    inference(subsumption_resolution,[],[f494,f196])).
% 2.19/0.73  fof(f494,plain,(
% 2.19/0.73    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl5_10 | ~spl5_11 | ~spl5_15)),
% 2.19/0.73    inference(subsumption_resolution,[],[f493,f191])).
% 2.19/0.73  fof(f493,plain,(
% 2.19/0.73    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl5_10 | ~spl5_15)),
% 2.19/0.73    inference(subsumption_resolution,[],[f490,f186])).
% 2.19/0.73  fof(f490,plain,(
% 2.19/0.73    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl5_15),
% 2.19/0.73    inference(resolution,[],[f489,f213])).
% 2.19/0.73  fof(f489,plain,(
% 2.19/0.73    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.73    inference(forward_demodulation,[],[f108,f110])).
% 2.19/0.73  fof(f108,plain,(
% 2.19/0.73    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.73    inference(cnf_transformation,[],[f54])).
% 2.19/0.73  fof(f54,plain,(
% 2.19/0.73    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/0.73    inference(flattening,[],[f53])).
% 2.19/0.73  fof(f53,plain,(
% 2.19/0.73    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.19/0.73    inference(ennf_transformation,[],[f27])).
% 2.77/0.73  fof(f27,axiom,(
% 2.77/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.77/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.77/0.73  fof(f485,plain,(
% 2.77/0.73    ~spl5_12 | ~spl5_17 | spl5_29),
% 2.77/0.73    inference(avatar_contradiction_clause,[],[f484])).
% 2.77/0.73  fof(f484,plain,(
% 2.77/0.73    $false | (~spl5_12 | ~spl5_17 | spl5_29)),
% 2.77/0.73    inference(subsumption_resolution,[],[f483,f231])).
% 2.77/0.73  fof(f483,plain,(
% 2.77/0.73    ~v1_relat_1(sK2) | (~spl5_12 | spl5_29)),
% 2.77/0.73    inference(subsumption_resolution,[],[f481,f196])).
% 2.77/0.73  fof(f481,plain,(
% 2.77/0.73    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_29),
% 2.77/0.73    inference(resolution,[],[f448,f93])).
% 2.77/0.73  fof(f448,plain,(
% 2.77/0.73    ~v1_relat_1(k2_funct_1(sK2)) | spl5_29),
% 2.77/0.73    inference(avatar_component_clause,[],[f446])).
% 2.77/0.73  fof(f446,plain,(
% 2.77/0.73    spl5_29 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.77/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.77/0.73  fof(f476,plain,(
% 2.77/0.73    ~spl5_29 | spl5_35 | ~spl5_17 | ~spl5_27),
% 2.77/0.73    inference(avatar_split_clause,[],[f471,f422,f229,f473,f446])).
% 2.77/0.73  fof(f422,plain,(
% 2.77/0.73    spl5_27 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.77/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 2.77/0.73  fof(f471,plain,(
% 2.77/0.73    r1_tarski(sK0,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_17 | ~spl5_27)),
% 2.77/0.73    inference(forward_demodulation,[],[f470,f118])).
% 2.77/0.73  fof(f470,plain,(
% 2.77/0.73    r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_17 | ~spl5_27)),
% 2.77/0.73    inference(subsumption_resolution,[],[f441,f231])).
% 2.77/0.73  fof(f441,plain,(
% 2.77/0.73    r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl5_27),
% 2.77/0.73    inference(superposition,[],[f123,f424])).
% 2.77/0.73  fof(f424,plain,(
% 2.77/0.73    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl5_27),
% 2.77/0.73    inference(avatar_component_clause,[],[f422])).
% 2.77/0.73  fof(f425,plain,(
% 2.77/0.73    spl5_27 | spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_12),
% 2.77/0.73    inference(avatar_split_clause,[],[f420,f194,f189,f184,f164,f154,f144,f422])).
% 2.77/0.73  fof(f144,plain,(
% 2.77/0.73    spl5_2 <=> k1_xboole_0 = sK1),
% 2.77/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.77/0.73  fof(f420,plain,(
% 2.77/0.73    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_12)),
% 2.77/0.73    inference(subsumption_resolution,[],[f419,f196])).
% 2.77/0.73  fof(f419,plain,(
% 2.77/0.73    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_10 | ~spl5_11)),
% 2.77/0.73    inference(subsumption_resolution,[],[f418,f191])).
% 2.77/0.73  fof(f418,plain,(
% 2.77/0.73    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_10)),
% 2.77/0.73    inference(subsumption_resolution,[],[f417,f186])).
% 2.77/0.73  fof(f417,plain,(
% 2.77/0.73    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl5_2 | ~spl5_4 | ~spl5_6)),
% 2.77/0.73    inference(subsumption_resolution,[],[f416,f156])).
% 2.77/0.73  fof(f416,plain,(
% 2.77/0.73    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl5_2 | ~spl5_6)),
% 2.77/0.73    inference(subsumption_resolution,[],[f415,f146])).
% 2.77/0.73  fof(f146,plain,(
% 2.77/0.73    k1_xboole_0 != sK1 | spl5_2),
% 2.77/0.73    inference(avatar_component_clause,[],[f144])).
% 2.77/0.73  fof(f415,plain,(
% 2.77/0.73    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_6),
% 2.77/0.73    inference(trivial_inequality_removal,[],[f412])).
% 2.77/0.73  fof(f412,plain,(
% 2.77/0.73    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_6),
% 2.77/0.73    inference(superposition,[],[f403,f166])).
% 2.77/0.73  fof(f395,plain,(
% 2.77/0.73    spl5_26 | ~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_12 | ~spl5_15),
% 2.77/0.73    inference(avatar_split_clause,[],[f390,f211,f194,f184,f179,f169,f392])).
% 2.77/0.73  fof(f390,plain,(
% 2.77/0.73    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_12 | ~spl5_15)),
% 2.77/0.73    inference(subsumption_resolution,[],[f389,f196])).
% 2.77/0.73  fof(f389,plain,(
% 2.77/0.73    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl5_7 | ~spl5_9 | ~spl5_10 | ~spl5_15)),
% 2.77/0.73    inference(subsumption_resolution,[],[f388,f186])).
% 2.77/0.73  fof(f388,plain,(
% 2.77/0.73    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_7 | ~spl5_9 | ~spl5_15)),
% 2.77/0.73    inference(subsumption_resolution,[],[f387,f181])).
% 2.77/0.73  fof(f387,plain,(
% 2.77/0.73    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_7 | ~spl5_15)),
% 2.77/0.73    inference(subsumption_resolution,[],[f384,f171])).
% 2.77/0.73  fof(f384,plain,(
% 2.77/0.73    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl5_15),
% 2.77/0.73    inference(superposition,[],[f213,f113])).
% 2.77/0.73  fof(f318,plain,(
% 2.77/0.73    spl5_22 | ~spl5_6 | ~spl5_10),
% 2.77/0.73    inference(avatar_split_clause,[],[f317,f184,f164,f313])).
% 2.77/0.73  fof(f317,plain,(
% 2.77/0.73    sK1 = k2_relat_1(sK2) | (~spl5_6 | ~spl5_10)),
% 2.77/0.73    inference(subsumption_resolution,[],[f310,f186])).
% 2.77/0.73  fof(f310,plain,(
% 2.77/0.73    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_6),
% 2.77/0.73    inference(superposition,[],[f166,f114])).
% 2.77/0.73  fof(f264,plain,(
% 2.77/0.73    spl5_19 | ~spl5_10),
% 2.77/0.73    inference(avatar_split_clause,[],[f253,f184,f261])).
% 2.77/0.73  fof(f253,plain,(
% 2.77/0.73    v4_relat_1(sK2,sK0) | ~spl5_10),
% 2.77/0.73    inference(resolution,[],[f131,f186])).
% 2.77/0.73  fof(f131,plain,(
% 2.77/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f65])).
% 2.77/0.73  fof(f65,plain,(
% 2.77/0.73    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.77/0.73    inference(ennf_transformation,[],[f33])).
% 2.77/0.73  fof(f33,plain,(
% 2.77/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.77/0.73    inference(pure_predicate_removal,[],[f20])).
% 2.77/0.73  fof(f20,axiom,(
% 2.77/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.77/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.77/0.73  fof(f259,plain,(
% 2.77/0.73    spl5_18 | ~spl5_7),
% 2.77/0.73    inference(avatar_split_clause,[],[f252,f169,f256])).
% 2.77/0.73  fof(f252,plain,(
% 2.77/0.73    v4_relat_1(sK3,sK1) | ~spl5_7),
% 2.77/0.73    inference(resolution,[],[f131,f171])).
% 2.77/0.73  fof(f232,plain,(
% 2.77/0.73    spl5_17 | ~spl5_10),
% 2.77/0.73    inference(avatar_split_clause,[],[f227,f184,f229])).
% 2.77/0.73  fof(f227,plain,(
% 2.77/0.73    v1_relat_1(sK2) | ~spl5_10),
% 2.77/0.73    inference(subsumption_resolution,[],[f219,f120])).
% 2.77/0.73  fof(f120,plain,(
% 2.77/0.73    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.77/0.73    inference(cnf_transformation,[],[f7])).
% 2.77/0.73  fof(f7,axiom,(
% 2.77/0.73    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.77/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.77/0.73  fof(f219,plain,(
% 2.77/0.73    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl5_10),
% 2.77/0.73    inference(resolution,[],[f119,f186])).
% 2.77/0.73  fof(f119,plain,(
% 2.77/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f62])).
% 2.77/0.73  fof(f62,plain,(
% 2.77/0.73    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.77/0.73    inference(ennf_transformation,[],[f5])).
% 2.77/0.73  fof(f5,axiom,(
% 2.77/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.77/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.77/0.73  fof(f226,plain,(
% 2.77/0.73    spl5_16 | ~spl5_7),
% 2.77/0.73    inference(avatar_split_clause,[],[f221,f169,f223])).
% 2.77/0.73  fof(f221,plain,(
% 2.77/0.73    v1_relat_1(sK3) | ~spl5_7),
% 2.77/0.73    inference(subsumption_resolution,[],[f218,f120])).
% 2.77/0.73  fof(f218,plain,(
% 2.77/0.73    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl5_7),
% 2.77/0.73    inference(resolution,[],[f119,f171])).
% 2.77/0.73  fof(f214,plain,(
% 2.77/0.73    spl5_15 | ~spl5_5),
% 2.77/0.73    inference(avatar_split_clause,[],[f209,f159,f211])).
% 2.77/0.73  fof(f159,plain,(
% 2.77/0.73    spl5_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.77/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.77/0.73  fof(f209,plain,(
% 2.77/0.73    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl5_5),
% 2.77/0.73    inference(backward_demodulation,[],[f161,f110])).
% 2.77/0.73  fof(f161,plain,(
% 2.77/0.73    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl5_5),
% 2.77/0.73    inference(avatar_component_clause,[],[f159])).
% 2.77/0.73  fof(f197,plain,(
% 2.77/0.73    spl5_12),
% 2.77/0.73    inference(avatar_split_clause,[],[f75,f194])).
% 2.77/0.73  fof(f75,plain,(
% 2.77/0.73    v1_funct_1(sK2)),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f68,plain,(
% 2.77/0.73    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.77/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f67,f66])).
% 2.77/0.73  fof(f66,plain,(
% 2.77/0.73    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.77/0.73    introduced(choice_axiom,[])).
% 2.77/0.73  fof(f67,plain,(
% 2.77/0.73    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.77/0.73    introduced(choice_axiom,[])).
% 2.77/0.73  fof(f35,plain,(
% 2.77/0.73    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.77/0.73    inference(flattening,[],[f34])).
% 2.77/0.73  fof(f34,plain,(
% 2.77/0.73    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.77/0.73    inference(ennf_transformation,[],[f31])).
% 2.77/0.73  fof(f31,negated_conjecture,(
% 2.77/0.73    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.77/0.73    inference(negated_conjecture,[],[f30])).
% 2.77/0.73  fof(f30,conjecture,(
% 2.77/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.77/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.77/0.73  fof(f192,plain,(
% 2.77/0.73    spl5_11),
% 2.77/0.73    inference(avatar_split_clause,[],[f76,f189])).
% 2.77/0.73  fof(f76,plain,(
% 2.77/0.73    v1_funct_2(sK2,sK0,sK1)),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f187,plain,(
% 2.77/0.73    spl5_10),
% 2.77/0.73    inference(avatar_split_clause,[],[f77,f184])).
% 2.77/0.73  fof(f77,plain,(
% 2.77/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f182,plain,(
% 2.77/0.73    spl5_9),
% 2.77/0.73    inference(avatar_split_clause,[],[f78,f179])).
% 2.77/0.73  fof(f78,plain,(
% 2.77/0.73    v1_funct_1(sK3)),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f177,plain,(
% 2.77/0.73    spl5_8),
% 2.77/0.73    inference(avatar_split_clause,[],[f79,f174])).
% 2.77/0.73  fof(f79,plain,(
% 2.77/0.73    v1_funct_2(sK3,sK1,sK0)),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f172,plain,(
% 2.77/0.73    spl5_7),
% 2.77/0.73    inference(avatar_split_clause,[],[f80,f169])).
% 2.77/0.73  fof(f80,plain,(
% 2.77/0.73    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f167,plain,(
% 2.77/0.73    spl5_6),
% 2.77/0.73    inference(avatar_split_clause,[],[f81,f164])).
% 2.77/0.73  fof(f81,plain,(
% 2.77/0.73    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f162,plain,(
% 2.77/0.73    spl5_5),
% 2.77/0.73    inference(avatar_split_clause,[],[f82,f159])).
% 2.77/0.73  fof(f82,plain,(
% 2.77/0.73    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f157,plain,(
% 2.77/0.73    spl5_4),
% 2.77/0.73    inference(avatar_split_clause,[],[f83,f154])).
% 2.77/0.73  fof(f83,plain,(
% 2.77/0.73    v2_funct_1(sK2)),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f152,plain,(
% 2.77/0.73    ~spl5_3),
% 2.77/0.73    inference(avatar_split_clause,[],[f84,f149])).
% 2.77/0.73  fof(f84,plain,(
% 2.77/0.73    k1_xboole_0 != sK0),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f147,plain,(
% 2.77/0.73    ~spl5_2),
% 2.77/0.73    inference(avatar_split_clause,[],[f85,f144])).
% 2.77/0.73  fof(f85,plain,(
% 2.77/0.73    k1_xboole_0 != sK1),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  fof(f142,plain,(
% 2.77/0.73    ~spl5_1),
% 2.77/0.73    inference(avatar_split_clause,[],[f86,f139])).
% 2.77/0.73  fof(f139,plain,(
% 2.77/0.73    spl5_1 <=> k2_funct_1(sK2) = sK3),
% 2.77/0.73    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.77/0.73  fof(f86,plain,(
% 2.77/0.73    k2_funct_1(sK2) != sK3),
% 2.77/0.73    inference(cnf_transformation,[],[f68])).
% 2.77/0.73  % SZS output end Proof for theBenchmark
% 2.77/0.73  % (29887)------------------------------
% 2.77/0.73  % (29887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.73  % (29887)Termination reason: Refutation
% 2.77/0.73  
% 2.77/0.73  % (29887)Memory used [KB]: 7419
% 2.77/0.73  % (29887)Time elapsed: 0.292 s
% 2.77/0.73  % (29887)------------------------------
% 2.77/0.73  % (29887)------------------------------
% 2.77/0.73  % (29865)Success in time 0.364 s
%------------------------------------------------------------------------------
