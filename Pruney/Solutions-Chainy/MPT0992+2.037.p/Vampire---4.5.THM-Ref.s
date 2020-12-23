%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:15 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  279 ( 558 expanded)
%              Number of leaves         :   61 ( 232 expanded)
%              Depth                    :   11
%              Number of atoms          :  835 (1753 expanded)
%              Number of equality atoms :  144 ( 382 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2291,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f116,f121,f126,f136,f145,f153,f163,f170,f242,f254,f278,f290,f309,f311,f321,f329,f345,f395,f431,f759,f774,f782,f853,f880,f885,f955,f958,f1009,f1044,f1306,f1339,f1507,f1834,f1881,f1915,f1931,f2101,f2175,f2186,f2190,f2211,f2221,f2282,f2290])).

fof(f2290,plain,
    ( ~ spl4_143
    | spl4_144
    | ~ spl4_152 ),
    inference(avatar_contradiction_clause,[],[f2289])).

fof(f2289,plain,
    ( $false
    | ~ spl4_143
    | spl4_144
    | ~ spl4_152 ),
    inference(subsumption_resolution,[],[f2286,f2220])).

fof(f2220,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_144 ),
    inference(avatar_component_clause,[],[f2218])).

fof(f2218,plain,
    ( spl4_144
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).

fof(f2286,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_143
    | ~ spl4_152 ),
    inference(resolution,[],[f2281,f2189])).

fof(f2189,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_143 ),
    inference(avatar_component_clause,[],[f2188])).

fof(f2188,plain,
    ( spl4_143
  <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).

fof(f2281,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6))) )
    | ~ spl4_152 ),
    inference(avatar_component_clause,[],[f2280])).

fof(f2280,plain,
    ( spl4_152
  <=> ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f2282,plain,
    ( spl4_152
    | ~ spl4_22
    | ~ spl4_100
    | ~ spl4_128
    | ~ spl4_139 ),
    inference(avatar_split_clause,[],[f2274,f2167,f1913,f1505,f298,f2280])).

fof(f298,plain,
    ( spl4_22
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1505,plain,
    ( spl4_100
  <=> ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f1913,plain,
    ( spl4_128
  <=> ! [X6] : v1_relat_1(k7_relat_1(sK3,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f2167,plain,
    ( spl4_139
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).

fof(f2274,plain,
    ( ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) )
    | ~ spl4_22
    | ~ spl4_100
    | ~ spl4_128
    | ~ spl4_139 ),
    inference(forward_demodulation,[],[f2037,f2169])).

fof(f2169,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_139 ),
    inference(avatar_component_clause,[],[f2167])).

fof(f2037,plain,
    ( ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) )
    | ~ spl4_22
    | ~ spl4_100
    | ~ spl4_128 ),
    inference(subsumption_resolution,[],[f2036,f1914])).

fof(f1914,plain,
    ( ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))
    | ~ spl4_128 ),
    inference(avatar_component_clause,[],[f1913])).

fof(f2036,plain,
    ( ! [X6] :
        ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
        | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) )
    | ~ spl4_22
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f2035,f1506])).

fof(f1506,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_100 ),
    inference(avatar_component_clause,[],[f1505])).

fof(f2035,plain,
    ( ! [X6] :
        ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6)))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_22
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f1986,f1506])).

fof(f1986,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)
        | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6)))
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_22
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f579,f1506])).

fof(f579,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6)
        | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6)))
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_22 ),
    inference(resolution,[],[f299,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f299,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f298])).

fof(f2221,plain,
    ( ~ spl4_144
    | spl4_24
    | ~ spl4_100 ),
    inference(avatar_split_clause,[],[f2213,f1505,f306,f2218])).

fof(f306,plain,
    ( spl4_24
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f2213,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_24
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f308,f1506])).

fof(f308,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f306])).

fof(f2211,plain,
    ( spl4_138
    | ~ spl4_142
    | ~ spl4_143 ),
    inference(avatar_contradiction_clause,[],[f2210])).

fof(f2210,plain,
    ( $false
    | spl4_138
    | ~ spl4_142
    | ~ spl4_143 ),
    inference(subsumption_resolution,[],[f2203,f2100])).

fof(f2100,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_138 ),
    inference(avatar_component_clause,[],[f2098])).

fof(f2098,plain,
    ( spl4_138
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f2203,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ spl4_142
    | ~ spl4_143 ),
    inference(resolution,[],[f2189,f2185])).

fof(f2185,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)
        | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10) )
    | ~ spl4_142 ),
    inference(avatar_component_clause,[],[f2184])).

fof(f2184,plain,
    ( spl4_142
  <=> ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f2190,plain,
    ( spl4_143
    | ~ spl4_128
    | ~ spl4_130 ),
    inference(avatar_split_clause,[],[f1939,f1929,f1913,f2188])).

fof(f1929,plain,
    ( spl4_130
  <=> ! [X4] : v5_relat_1(k7_relat_1(sK3,X4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f1939,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_128
    | ~ spl4_130 ),
    inference(subsumption_resolution,[],[f1937,f1914])).

fof(f1937,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl4_130 ),
    inference(resolution,[],[f1930,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1930,plain,
    ( ! [X4] : v5_relat_1(k7_relat_1(sK3,X4),sK1)
    | ~ spl4_130 ),
    inference(avatar_component_clause,[],[f1929])).

fof(f2186,plain,
    ( spl4_142
    | ~ spl4_22
    | ~ spl4_100
    | ~ spl4_128
    | ~ spl4_139 ),
    inference(avatar_split_clause,[],[f2177,f2167,f1913,f1505,f298,f2184])).

fof(f2177,plain,
    ( ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) )
    | ~ spl4_22
    | ~ spl4_100
    | ~ spl4_128
    | ~ spl4_139 ),
    inference(forward_demodulation,[],[f2057,f2169])).

fof(f2057,plain,
    ( ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) )
    | ~ spl4_22
    | ~ spl4_100
    | ~ spl4_128 ),
    inference(subsumption_resolution,[],[f2056,f1914])).

fof(f2056,plain,
    ( ! [X10] :
        ( ~ v1_relat_1(k7_relat_1(sK3,sK2))
        | v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) )
    | ~ spl4_22
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f2055,f1506])).

fof(f2055,plain,
    ( ! [X10] :
        ( v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_22
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f1712,f1506])).

fof(f1712,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)
        | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_22
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f362,f1506])).

fof(f362,plain,
    ( ! [X10] :
        ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10)
        | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10)
        | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    | ~ spl4_22 ),
    inference(resolution,[],[f299,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2175,plain,
    ( spl4_139
    | ~ spl4_2
    | ~ spl4_125 ),
    inference(avatar_split_clause,[],[f2124,f1832,f113,f2167])).

fof(f113,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1832,plain,
    ( spl4_125
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_125])])).

fof(f2124,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_2
    | ~ spl4_125 ),
    inference(resolution,[],[f115,f1833])).

fof(f1833,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_125 ),
    inference(avatar_component_clause,[],[f1832])).

fof(f115,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f2101,plain,
    ( ~ spl4_138
    | spl4_23
    | ~ spl4_100 ),
    inference(avatar_split_clause,[],[f2079,f1505,f302,f2098])).

fof(f302,plain,
    ( spl4_23
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f2079,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_23
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f304,f1506])).

fof(f304,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f302])).

fof(f1931,plain,
    ( spl4_130
    | ~ spl4_127 ),
    inference(avatar_split_clause,[],[f1895,f1879,f1929])).

fof(f1879,plain,
    ( spl4_127
  <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).

fof(f1895,plain,
    ( ! [X4] : v5_relat_1(k7_relat_1(sK3,X4),sK1)
    | ~ spl4_127 ),
    inference(resolution,[],[f1880,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1880,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_127 ),
    inference(avatar_component_clause,[],[f1879])).

fof(f1915,plain,
    ( spl4_128
    | ~ spl4_127 ),
    inference(avatar_split_clause,[],[f1897,f1879,f1913])).

fof(f1897,plain,
    ( ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))
    | ~ spl4_127 ),
    inference(resolution,[],[f1880,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1881,plain,
    ( spl4_127
    | ~ spl4_6
    | ~ spl4_84
    | ~ spl4_100 ),
    inference(avatar_split_clause,[],[f1869,f1505,f1335,f133,f1879])).

fof(f133,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1335,plain,
    ( spl4_84
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f1869,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_84
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f1344,f1506])).

fof(f1344,plain,
    ( ! [X0] : m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_84 ),
    inference(resolution,[],[f1336,f135])).

fof(f135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1336,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f1335])).

fof(f1834,plain,
    ( spl4_125
    | ~ spl4_10
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f1820,f326,f160,f1832])).

fof(f160,plain,
    ( spl4_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f326,plain,
    ( spl4_26
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1820,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_10
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f215,f328])).

fof(f328,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f326])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK3))
        | k1_relat_1(k7_relat_1(sK3,X0)) = X0 )
    | ~ spl4_10 ),
    inference(resolution,[],[f68,f162])).

fof(f162,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f1507,plain,
    ( spl4_100
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f1329,f1294,f133,f1505])).

fof(f1294,plain,
    ( spl4_80
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1329,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | ~ spl4_6
    | ~ spl4_80 ),
    inference(resolution,[],[f1295,f135])).

fof(f1295,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) )
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f1294])).

fof(f1339,plain,
    ( spl4_84
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f1064,f108,f1335])).

fof(f108,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1064,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f110,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f110,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1306,plain,
    ( spl4_80
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f1065,f108,f1294])).

fof(f1065,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k2_partfun1(X3,X4,sK3,X5) = k7_relat_1(sK3,X5) )
    | ~ spl4_1 ),
    inference(resolution,[],[f110,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f1044,plain,
    ( ~ spl4_16
    | ~ spl4_65
    | spl4_67 ),
    inference(avatar_contradiction_clause,[],[f1043])).

fof(f1043,plain,
    ( $false
    | ~ spl4_16
    | ~ spl4_65
    | spl4_67 ),
    inference(subsumption_resolution,[],[f1042,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1042,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16
    | ~ spl4_65
    | spl4_67 ),
    inference(forward_demodulation,[],[f1037,f241])).

fof(f241,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl4_16
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1037,plain,
    ( ~ m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_65
    | spl4_67 ),
    inference(backward_demodulation,[],[f1008,f954])).

fof(f954,plain,
    ( ! [X4,X5,X3] : k7_relat_1(k1_xboole_0,X5) = k2_partfun1(X3,X4,k1_xboole_0,X5)
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f953])).

fof(f953,plain,
    ( spl4_65
  <=> ! [X3,X5,X4] : k7_relat_1(k1_xboole_0,X5) = k2_partfun1(X3,X4,k1_xboole_0,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f1008,plain,
    ( ~ m1_subset_1(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_67 ),
    inference(avatar_component_clause,[],[f1006])).

fof(f1006,plain,
    ( spl4_67
  <=> m1_subset_1(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f1009,plain,
    ( ~ spl4_67
    | ~ spl4_8
    | spl4_24
    | ~ spl4_51
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f966,f843,f756,f306,f142,f1006])).

fof(f142,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f756,plain,
    ( spl4_51
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f843,plain,
    ( spl4_59
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f966,plain,
    ( ~ m1_subset_1(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8
    | spl4_24
    | ~ spl4_51
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f965,f144])).

fof(f144,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f965,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_24
    | ~ spl4_51
    | ~ spl4_59 ),
    inference(forward_demodulation,[],[f964,f845])).

fof(f845,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f843])).

fof(f964,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl4_24
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f963,f101])).

fof(f101,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f963,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl4_24
    | ~ spl4_51 ),
    inference(forward_demodulation,[],[f308,f758])).

fof(f758,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f756])).

fof(f958,plain,
    ( ~ spl4_16
    | ~ spl4_21
    | ~ spl4_60
    | spl4_63 ),
    inference(avatar_contradiction_clause,[],[f957])).

fof(f957,plain,
    ( $false
    | ~ spl4_16
    | ~ spl4_21
    | ~ spl4_60
    | spl4_63 ),
    inference(subsumption_resolution,[],[f956,f289])).

fof(f289,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl4_21
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f956,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_16
    | ~ spl4_60
    | spl4_63 ),
    inference(forward_demodulation,[],[f951,f241])).

fof(f951,plain,
    ( ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)
    | ~ spl4_60
    | spl4_63 ),
    inference(backward_demodulation,[],[f884,f860])).

fof(f860,plain,
    ( ! [X4,X5,X3] : k7_relat_1(k1_xboole_0,X5) = k2_partfun1(X3,X4,k1_xboole_0,X5)
    | ~ spl4_60 ),
    inference(subsumption_resolution,[],[f855,f65])).

fof(f855,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k7_relat_1(k1_xboole_0,X5) = k2_partfun1(X3,X4,k1_xboole_0,X5) )
    | ~ spl4_60 ),
    inference(resolution,[],[f852,f95])).

fof(f852,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f850])).

fof(f850,plain,
    ( spl4_60
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f884,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_63 ),
    inference(avatar_component_clause,[],[f882])).

fof(f882,plain,
    ( spl4_63
  <=> v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f955,plain,
    ( spl4_65
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f860,f850,f953])).

fof(f885,plain,
    ( ~ spl4_63
    | ~ spl4_52
    | spl4_53 ),
    inference(avatar_split_clause,[],[f840,f771,f766,f882])).

fof(f766,plain,
    ( spl4_52
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f771,plain,
    ( spl4_53
  <=> v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f840,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)
    | ~ spl4_52
    | spl4_53 ),
    inference(backward_demodulation,[],[f773,f793])).

fof(f793,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_52 ),
    inference(resolution,[],[f768,f180])).

fof(f180,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f768,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f766])).

fof(f773,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)
    | spl4_53 ),
    inference(avatar_component_clause,[],[f771])).

fof(f880,plain,
    ( spl4_59
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f798,f766,f843])).

fof(f798,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f796,f64])).

fof(f796,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK3
    | ~ spl4_52 ),
    inference(resolution,[],[f768,f76])).

fof(f853,plain,
    ( spl4_60
    | ~ spl4_1
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f833,f766,f108,f850])).

fof(f833,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_52 ),
    inference(backward_demodulation,[],[f110,f793])).

fof(f782,plain,
    ( spl4_52
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f706,f150,f142,f766])).

fof(f150,plain,
    ( spl4_9
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f706,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f705,f101])).

fof(f705,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f152,f144])).

fof(f152,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f774,plain,
    ( ~ spl4_53
    | ~ spl4_8
    | spl4_30 ),
    inference(avatar_split_clause,[],[f701,f428,f142,f771])).

fof(f428,plain,
    ( spl4_30
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f701,plain,
    ( ~ v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)
    | ~ spl4_8
    | spl4_30 ),
    inference(forward_demodulation,[],[f430,f144])).

fof(f430,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK0),sK0,sK1)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f428])).

fof(f759,plain,
    ( spl4_51
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f686,f392,f756])).

fof(f392,plain,
    ( spl4_28
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f686,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f684,f64])).

fof(f684,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_28 ),
    inference(resolution,[],[f394,f76])).

fof(f394,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f392])).

fof(f431,plain,
    ( ~ spl4_30
    | ~ spl4_17
    | spl4_23 ),
    inference(avatar_split_clause,[],[f424,f302,f247,f428])).

fof(f247,plain,
    ( spl4_17
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f424,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK0),sK0,sK1)
    | ~ spl4_17
    | spl4_23 ),
    inference(forward_demodulation,[],[f304,f249])).

fof(f249,plain,
    ( sK0 = sK2
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f247])).

fof(f395,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f387,f142,f113,f392])).

fof(f387,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f115,f144])).

fof(f345,plain,
    ( ~ spl4_8
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl4_8
    | spl4_18 ),
    inference(subsumption_resolution,[],[f342,f64])).

fof(f342,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_8
    | spl4_18 ),
    inference(backward_demodulation,[],[f253,f144])).

fof(f253,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_18
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f329,plain,
    ( spl4_26
    | ~ spl4_6
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f324,f318,f133,f326])).

fof(f318,plain,
    ( spl4_25
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f324,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f225,f320])).

fof(f320,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f318])).

fof(f225,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f84,f135])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f321,plain,
    ( spl4_25
    | ~ spl4_3
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f286,f138,f133,f118,f318])).

fof(f118,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f138,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f286,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_3
    | ~ spl4_6
    | spl4_7 ),
    inference(subsumption_resolution,[],[f285,f135])).

fof(f285,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3
    | spl4_7 ),
    inference(subsumption_resolution,[],[f283,f140])).

fof(f140,plain,
    ( k1_xboole_0 != sK1
    | spl4_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f283,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(resolution,[],[f87,f120])).

fof(f120,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f311,plain,
    ( ~ spl4_1
    | ~ spl4_6
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6
    | spl4_22 ),
    inference(unit_resulting_resolution,[],[f110,f135,f300,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f300,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f298])).

fof(f309,plain,
    ( ~ spl4_22
    | ~ spl4_23
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f61,f306,f302,f298])).

fof(f61,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f290,plain,
    ( spl4_21
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f282,f276,f288])).

fof(f276,plain,
    ( spl4_20
  <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f282,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f281,f65])).

fof(f281,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f280])).

fof(f280,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_20 ),
    inference(superposition,[],[f265,f277])).

fof(f277,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f276])).

fof(f265,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f105,f101])).

fof(f105,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f278,plain,
    ( spl4_20
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f229,f123,f276])).

fof(f123,plain,
    ( spl4_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f229,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f224,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f224,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f84,f65])).

fof(f254,plain,
    ( spl4_17
    | ~ spl4_18
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f181,f113,f251,f247])).

fof(f181,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2
    | ~ spl4_2 ),
    inference(resolution,[],[f76,f115])).

fof(f242,plain,
    ( spl4_16
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f178,f167,f123,f239])).

fof(f167,plain,
    ( spl4_11
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f178,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f174,f125])).

fof(f174,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | ~ spl4_11 ),
    inference(resolution,[],[f169,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f169,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f170,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f154,f167])).

fof(f154,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f83,f65])).

fof(f163,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f155,f133,f160])).

fof(f155,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f83,f135])).

fof(f153,plain,
    ( spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f147,f133,f150])).

fof(f147,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f77,f135])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f145,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f60,f142,f138])).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f136,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f58,f133])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f126,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f62,f123])).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f121,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f57,f118])).

fof(f57,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f116,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f59,f113])).

fof(f59,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f111,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f56,f108])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:32:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (28523)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (28521)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (28533)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (28524)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (28531)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (28525)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (28542)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (28526)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (28535)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (28545)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (28540)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (28543)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.55/0.56  % (28532)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.55/0.56  % (28539)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.55/0.57  % (28529)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.71/0.58  % (28522)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.71/0.58  % (28544)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.71/0.58  % (28536)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.71/0.59  % (28534)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.71/0.59  % (28530)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.71/0.59  % (28541)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.71/0.59  % (28527)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.71/0.60  % (28528)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.71/0.60  % (28537)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.71/0.60  % (28538)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.71/0.62  % (28546)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.71/0.62  % (28523)Refutation found. Thanks to Tanya!
% 1.71/0.62  % SZS status Theorem for theBenchmark
% 1.71/0.62  % SZS output start Proof for theBenchmark
% 1.71/0.62  fof(f2291,plain,(
% 1.71/0.62    $false),
% 1.71/0.62    inference(avatar_sat_refutation,[],[f111,f116,f121,f126,f136,f145,f153,f163,f170,f242,f254,f278,f290,f309,f311,f321,f329,f345,f395,f431,f759,f774,f782,f853,f880,f885,f955,f958,f1009,f1044,f1306,f1339,f1507,f1834,f1881,f1915,f1931,f2101,f2175,f2186,f2190,f2211,f2221,f2282,f2290])).
% 1.71/0.62  fof(f2290,plain,(
% 1.71/0.62    ~spl4_143 | spl4_144 | ~spl4_152),
% 1.71/0.62    inference(avatar_contradiction_clause,[],[f2289])).
% 1.71/0.62  fof(f2289,plain,(
% 1.71/0.62    $false | (~spl4_143 | spl4_144 | ~spl4_152)),
% 1.71/0.62    inference(subsumption_resolution,[],[f2286,f2220])).
% 1.71/0.62  fof(f2220,plain,(
% 1.71/0.62    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_144),
% 1.71/0.62    inference(avatar_component_clause,[],[f2218])).
% 1.71/0.62  fof(f2218,plain,(
% 1.71/0.62    spl4_144 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).
% 1.71/0.62  fof(f2286,plain,(
% 1.71/0.62    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_143 | ~spl4_152)),
% 1.71/0.62    inference(resolution,[],[f2281,f2189])).
% 1.71/0.62  fof(f2189,plain,(
% 1.71/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | ~spl4_143),
% 1.71/0.62    inference(avatar_component_clause,[],[f2188])).
% 1.71/0.62  fof(f2188,plain,(
% 1.71/0.62    spl4_143 <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).
% 1.71/0.62  fof(f2281,plain,(
% 1.71/0.62    ( ! [X6] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6)))) ) | ~spl4_152),
% 1.71/0.62    inference(avatar_component_clause,[],[f2280])).
% 1.71/0.62  fof(f2280,plain,(
% 1.71/0.62    spl4_152 <=> ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).
% 1.71/0.62  fof(f2282,plain,(
% 1.71/0.62    spl4_152 | ~spl4_22 | ~spl4_100 | ~spl4_128 | ~spl4_139),
% 1.71/0.62    inference(avatar_split_clause,[],[f2274,f2167,f1913,f1505,f298,f2280])).
% 1.71/0.62  fof(f298,plain,(
% 1.71/0.62    spl4_22 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.71/0.62  fof(f1505,plain,(
% 1.71/0.62    spl4_100 <=> ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).
% 1.71/0.62  fof(f1913,plain,(
% 1.71/0.62    spl4_128 <=> ! [X6] : v1_relat_1(k7_relat_1(sK3,X6))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).
% 1.71/0.62  fof(f2167,plain,(
% 1.71/0.62    spl4_139 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).
% 1.71/0.62  fof(f2274,plain,(
% 1.71/0.62    ( ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)) ) | (~spl4_22 | ~spl4_100 | ~spl4_128 | ~spl4_139)),
% 1.71/0.62    inference(forward_demodulation,[],[f2037,f2169])).
% 1.71/0.62  fof(f2169,plain,(
% 1.71/0.62    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_139),
% 1.71/0.62    inference(avatar_component_clause,[],[f2167])).
% 1.71/0.62  fof(f2037,plain,(
% 1.71/0.62    ( ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)) ) | (~spl4_22 | ~spl4_100 | ~spl4_128)),
% 1.71/0.62    inference(subsumption_resolution,[],[f2036,f1914])).
% 1.71/0.62  fof(f1914,plain,(
% 1.71/0.62    ( ! [X6] : (v1_relat_1(k7_relat_1(sK3,X6))) ) | ~spl4_128),
% 1.71/0.62    inference(avatar_component_clause,[],[f1913])).
% 1.71/0.62  fof(f2036,plain,(
% 1.71/0.62    ( ! [X6] : (~v1_relat_1(k7_relat_1(sK3,sK2)) | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6)) ) | (~spl4_22 | ~spl4_100)),
% 1.71/0.62    inference(forward_demodulation,[],[f2035,f1506])).
% 1.71/0.62  fof(f1506,plain,(
% 1.71/0.62    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | ~spl4_100),
% 1.71/0.62    inference(avatar_component_clause,[],[f1505])).
% 1.71/0.62  fof(f2035,plain,(
% 1.71/0.62    ( ! [X6] : (m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,sK2)),X6))) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | (~spl4_22 | ~spl4_100)),
% 1.71/0.62    inference(forward_demodulation,[],[f1986,f1506])).
% 1.71/0.62  fof(f1986,plain,(
% 1.71/0.62    ( ! [X6] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X6) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6))) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | (~spl4_22 | ~spl4_100)),
% 1.71/0.62    inference(forward_demodulation,[],[f579,f1506])).
% 1.71/0.62  fof(f579,plain,(
% 1.71/0.62    ( ! [X6] : (~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6) | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X6))) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | ~spl4_22),
% 1.71/0.62    inference(resolution,[],[f299,f73])).
% 1.71/0.62  fof(f73,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f31])).
% 1.71/0.62  fof(f31,plain,(
% 1.71/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.71/0.62    inference(flattening,[],[f30])).
% 1.71/0.62  fof(f30,plain,(
% 1.71/0.62    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.71/0.62    inference(ennf_transformation,[],[f20])).
% 1.71/0.62  fof(f20,axiom,(
% 1.71/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.71/0.62  fof(f299,plain,(
% 1.71/0.62    v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | ~spl4_22),
% 1.71/0.62    inference(avatar_component_clause,[],[f298])).
% 1.71/0.62  fof(f2221,plain,(
% 1.71/0.62    ~spl4_144 | spl4_24 | ~spl4_100),
% 1.71/0.62    inference(avatar_split_clause,[],[f2213,f1505,f306,f2218])).
% 1.71/0.62  fof(f306,plain,(
% 1.71/0.62    spl4_24 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.71/0.62  fof(f2213,plain,(
% 1.71/0.62    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_24 | ~spl4_100)),
% 1.71/0.62    inference(forward_demodulation,[],[f308,f1506])).
% 1.71/0.62  fof(f308,plain,(
% 1.71/0.62    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_24),
% 1.71/0.62    inference(avatar_component_clause,[],[f306])).
% 1.71/0.62  fof(f2211,plain,(
% 1.71/0.62    spl4_138 | ~spl4_142 | ~spl4_143),
% 1.71/0.62    inference(avatar_contradiction_clause,[],[f2210])).
% 1.71/0.62  fof(f2210,plain,(
% 1.71/0.62    $false | (spl4_138 | ~spl4_142 | ~spl4_143)),
% 1.71/0.62    inference(subsumption_resolution,[],[f2203,f2100])).
% 1.71/0.62  fof(f2100,plain,(
% 1.71/0.62    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | spl4_138),
% 1.71/0.62    inference(avatar_component_clause,[],[f2098])).
% 1.71/0.62  fof(f2098,plain,(
% 1.71/0.62    spl4_138 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).
% 1.71/0.62  fof(f2203,plain,(
% 1.71/0.62    v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (~spl4_142 | ~spl4_143)),
% 1.71/0.62    inference(resolution,[],[f2189,f2185])).
% 1.71/0.62  fof(f2185,plain,(
% 1.71/0.62    ( ! [X10] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) | v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10)) ) | ~spl4_142),
% 1.71/0.62    inference(avatar_component_clause,[],[f2184])).
% 1.71/0.62  fof(f2184,plain,(
% 1.71/0.62    spl4_142 <=> ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10))),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).
% 1.71/0.62  fof(f2190,plain,(
% 1.71/0.62    spl4_143 | ~spl4_128 | ~spl4_130),
% 1.71/0.62    inference(avatar_split_clause,[],[f1939,f1929,f1913,f2188])).
% 1.71/0.62  fof(f1929,plain,(
% 1.71/0.62    spl4_130 <=> ! [X4] : v5_relat_1(k7_relat_1(sK3,X4),sK1)),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).
% 1.71/0.62  fof(f1939,plain,(
% 1.71/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | (~spl4_128 | ~spl4_130)),
% 1.71/0.62    inference(subsumption_resolution,[],[f1937,f1914])).
% 1.71/0.62  fof(f1937,plain,(
% 1.71/0.62    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | ~spl4_130),
% 1.71/0.62    inference(resolution,[],[f1930,f69])).
% 1.71/0.62  fof(f69,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f49])).
% 1.71/0.62  fof(f49,plain,(
% 1.71/0.62    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.71/0.62    inference(nnf_transformation,[],[f29])).
% 1.71/0.62  fof(f29,plain,(
% 1.71/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.71/0.62    inference(ennf_transformation,[],[f8])).
% 1.71/0.62  fof(f8,axiom,(
% 1.71/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.71/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.71/0.62  fof(f1930,plain,(
% 1.71/0.62    ( ! [X4] : (v5_relat_1(k7_relat_1(sK3,X4),sK1)) ) | ~spl4_130),
% 1.71/0.62    inference(avatar_component_clause,[],[f1929])).
% 1.71/0.62  fof(f2186,plain,(
% 1.71/0.62    spl4_142 | ~spl4_22 | ~spl4_100 | ~spl4_128 | ~spl4_139),
% 1.71/0.62    inference(avatar_split_clause,[],[f2177,f2167,f1913,f1505,f298,f2184])).
% 1.71/0.62  fof(f2177,plain,(
% 1.71/0.62    ( ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),sK2,X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)) ) | (~spl4_22 | ~spl4_100 | ~spl4_128 | ~spl4_139)),
% 1.71/0.62    inference(forward_demodulation,[],[f2057,f2169])).
% 1.71/0.62  fof(f2057,plain,(
% 1.71/0.62    ( ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)) ) | (~spl4_22 | ~spl4_100 | ~spl4_128)),
% 1.71/0.62    inference(subsumption_resolution,[],[f2056,f1914])).
% 1.71/0.62  fof(f2056,plain,(
% 1.71/0.62    ( ! [X10] : (~v1_relat_1(k7_relat_1(sK3,sK2)) | v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10)) ) | (~spl4_22 | ~spl4_100)),
% 1.71/0.62    inference(forward_demodulation,[],[f2055,f1506])).
% 1.71/0.62  fof(f2055,plain,(
% 1.71/0.62    ( ! [X10] : (v1_funct_2(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)),X10) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | (~spl4_22 | ~spl4_100)),
% 1.71/0.62    inference(forward_demodulation,[],[f1712,f1506])).
% 1.71/0.62  fof(f1712,plain,(
% 1.71/0.62    ( ! [X10] : (~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X10) | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | (~spl4_22 | ~spl4_100)),
% 1.71/0.62    inference(forward_demodulation,[],[f362,f1506])).
% 1.71/0.62  fof(f362,plain,(
% 1.71/0.62    ( ! [X10] : (~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10) | v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),X10) | ~v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))) ) | ~spl4_22),
% 1.71/0.62    inference(resolution,[],[f299,f72])).
% 1.71/0.62  fof(f72,plain,(
% 1.71/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.71/0.62    inference(cnf_transformation,[],[f31])).
% 1.71/0.62  fof(f2175,plain,(
% 1.71/0.62    spl4_139 | ~spl4_2 | ~spl4_125),
% 1.71/0.62    inference(avatar_split_clause,[],[f2124,f1832,f113,f2167])).
% 1.71/0.62  fof(f113,plain,(
% 1.71/0.62    spl4_2 <=> r1_tarski(sK2,sK0)),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.71/0.62  fof(f1832,plain,(
% 1.71/0.62    spl4_125 <=> ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0)),
% 1.71/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_125])])).
% 1.71/0.63  fof(f2124,plain,(
% 1.71/0.63    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_2 | ~spl4_125)),
% 1.71/0.63    inference(resolution,[],[f115,f1833])).
% 1.71/0.63  fof(f1833,plain,(
% 1.71/0.63    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_125),
% 1.71/0.63    inference(avatar_component_clause,[],[f1832])).
% 1.71/0.63  fof(f115,plain,(
% 1.71/0.63    r1_tarski(sK2,sK0) | ~spl4_2),
% 1.71/0.63    inference(avatar_component_clause,[],[f113])).
% 1.71/0.63  fof(f2101,plain,(
% 1.71/0.63    ~spl4_138 | spl4_23 | ~spl4_100),
% 1.71/0.63    inference(avatar_split_clause,[],[f2079,f1505,f302,f2098])).
% 1.71/0.63  fof(f302,plain,(
% 1.71/0.63    spl4_23 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.71/0.63  fof(f2079,plain,(
% 1.71/0.63    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (spl4_23 | ~spl4_100)),
% 1.71/0.63    inference(forward_demodulation,[],[f304,f1506])).
% 1.71/0.63  fof(f304,plain,(
% 1.71/0.63    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_23),
% 1.71/0.63    inference(avatar_component_clause,[],[f302])).
% 1.71/0.63  fof(f1931,plain,(
% 1.71/0.63    spl4_130 | ~spl4_127),
% 1.71/0.63    inference(avatar_split_clause,[],[f1895,f1879,f1929])).
% 1.71/0.63  fof(f1879,plain,(
% 1.71/0.63    spl4_127 <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_127])])).
% 1.71/0.63  fof(f1895,plain,(
% 1.71/0.63    ( ! [X4] : (v5_relat_1(k7_relat_1(sK3,X4),sK1)) ) | ~spl4_127),
% 1.71/0.63    inference(resolution,[],[f1880,f86])).
% 1.71/0.63  fof(f86,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f36])).
% 1.71/0.63  fof(f36,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(ennf_transformation,[],[f15])).
% 1.71/0.63  fof(f15,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.71/0.63  fof(f1880,plain,(
% 1.71/0.63    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_127),
% 1.71/0.63    inference(avatar_component_clause,[],[f1879])).
% 1.71/0.63  fof(f1915,plain,(
% 1.71/0.63    spl4_128 | ~spl4_127),
% 1.71/0.63    inference(avatar_split_clause,[],[f1897,f1879,f1913])).
% 1.71/0.63  fof(f1897,plain,(
% 1.71/0.63    ( ! [X6] : (v1_relat_1(k7_relat_1(sK3,X6))) ) | ~spl4_127),
% 1.71/0.63    inference(resolution,[],[f1880,f83])).
% 1.71/0.63  fof(f83,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f34])).
% 1.71/0.63  fof(f34,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(ennf_transformation,[],[f14])).
% 1.71/0.63  fof(f14,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.71/0.63  fof(f1881,plain,(
% 1.71/0.63    spl4_127 | ~spl4_6 | ~spl4_84 | ~spl4_100),
% 1.71/0.63    inference(avatar_split_clause,[],[f1869,f1505,f1335,f133,f1879])).
% 1.71/0.63  fof(f133,plain,(
% 1.71/0.63    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.71/0.63  fof(f1335,plain,(
% 1.71/0.63    spl4_84 <=> ! [X1,X0,X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 1.71/0.63  fof(f1869,plain,(
% 1.71/0.63    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_6 | ~spl4_84 | ~spl4_100)),
% 1.71/0.63    inference(forward_demodulation,[],[f1344,f1506])).
% 1.71/0.63  fof(f1344,plain,(
% 1.71/0.63    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | (~spl4_6 | ~spl4_84)),
% 1.71/0.63    inference(resolution,[],[f1336,f135])).
% 1.71/0.63  fof(f135,plain,(
% 1.71/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 1.71/0.63    inference(avatar_component_clause,[],[f133])).
% 1.71/0.63  fof(f1336,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_84),
% 1.71/0.63    inference(avatar_component_clause,[],[f1335])).
% 1.71/0.63  fof(f1834,plain,(
% 1.71/0.63    spl4_125 | ~spl4_10 | ~spl4_26),
% 1.71/0.63    inference(avatar_split_clause,[],[f1820,f326,f160,f1832])).
% 1.71/0.63  fof(f160,plain,(
% 1.71/0.63    spl4_10 <=> v1_relat_1(sK3)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.71/0.63  fof(f326,plain,(
% 1.71/0.63    spl4_26 <=> sK0 = k1_relat_1(sK3)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.71/0.63  fof(f1820,plain,(
% 1.71/0.63    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | (~spl4_10 | ~spl4_26)),
% 1.71/0.63    inference(forward_demodulation,[],[f215,f328])).
% 1.71/0.63  fof(f328,plain,(
% 1.71/0.63    sK0 = k1_relat_1(sK3) | ~spl4_26),
% 1.71/0.63    inference(avatar_component_clause,[],[f326])).
% 1.71/0.63  fof(f215,plain,(
% 1.71/0.63    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK3)) | k1_relat_1(k7_relat_1(sK3,X0)) = X0) ) | ~spl4_10),
% 1.71/0.63    inference(resolution,[],[f68,f162])).
% 1.71/0.63  fof(f162,plain,(
% 1.71/0.63    v1_relat_1(sK3) | ~spl4_10),
% 1.71/0.63    inference(avatar_component_clause,[],[f160])).
% 1.71/0.63  fof(f68,plain,(
% 1.71/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.71/0.63    inference(cnf_transformation,[],[f28])).
% 1.71/0.63  fof(f28,plain,(
% 1.71/0.63    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.71/0.63    inference(flattening,[],[f27])).
% 1.71/0.63  fof(f27,plain,(
% 1.71/0.63    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.71/0.63    inference(ennf_transformation,[],[f11])).
% 1.71/0.63  fof(f11,axiom,(
% 1.71/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.71/0.63  fof(f1507,plain,(
% 1.71/0.63    spl4_100 | ~spl4_6 | ~spl4_80),
% 1.71/0.63    inference(avatar_split_clause,[],[f1329,f1294,f133,f1505])).
% 1.71/0.63  fof(f1294,plain,(
% 1.71/0.63    spl4_80 <=> ! [X1,X0,X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 1.71/0.63  fof(f1329,plain,(
% 1.71/0.63    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)) ) | (~spl4_6 | ~spl4_80)),
% 1.71/0.63    inference(resolution,[],[f1295,f135])).
% 1.71/0.63  fof(f1295,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) ) | ~spl4_80),
% 1.71/0.63    inference(avatar_component_clause,[],[f1294])).
% 1.71/0.63  fof(f1339,plain,(
% 1.71/0.63    spl4_84 | ~spl4_1),
% 1.71/0.63    inference(avatar_split_clause,[],[f1064,f108,f1335])).
% 1.71/0.63  fof(f108,plain,(
% 1.71/0.63    spl4_1 <=> v1_funct_1(sK3)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.71/0.63  fof(f1064,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_1),
% 1.71/0.63    inference(resolution,[],[f110,f97])).
% 1.71/0.63  fof(f97,plain,(
% 1.71/0.63    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.63    inference(cnf_transformation,[],[f46])).
% 1.71/0.63  fof(f46,plain,(
% 1.71/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.71/0.63    inference(flattening,[],[f45])).
% 1.71/0.63  fof(f45,plain,(
% 1.71/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.71/0.63    inference(ennf_transformation,[],[f18])).
% 1.71/0.63  fof(f18,axiom,(
% 1.71/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.71/0.63  fof(f110,plain,(
% 1.71/0.63    v1_funct_1(sK3) | ~spl4_1),
% 1.71/0.63    inference(avatar_component_clause,[],[f108])).
% 1.71/0.63  fof(f1306,plain,(
% 1.71/0.63    spl4_80 | ~spl4_1),
% 1.71/0.63    inference(avatar_split_clause,[],[f1065,f108,f1294])).
% 1.71/0.63  fof(f1065,plain,(
% 1.71/0.63    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_partfun1(X3,X4,sK3,X5) = k7_relat_1(sK3,X5)) ) | ~spl4_1),
% 1.71/0.63    inference(resolution,[],[f110,f95])).
% 1.71/0.63  fof(f95,plain,(
% 1.71/0.63    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f44])).
% 1.71/0.63  fof(f44,plain,(
% 1.71/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.71/0.63    inference(flattening,[],[f43])).
% 1.71/0.63  fof(f43,plain,(
% 1.71/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.71/0.63    inference(ennf_transformation,[],[f19])).
% 1.71/0.63  fof(f19,axiom,(
% 1.71/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.71/0.63  fof(f1044,plain,(
% 1.71/0.63    ~spl4_16 | ~spl4_65 | spl4_67),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f1043])).
% 1.71/0.63  fof(f1043,plain,(
% 1.71/0.63    $false | (~spl4_16 | ~spl4_65 | spl4_67)),
% 1.71/0.63    inference(subsumption_resolution,[],[f1042,f65])).
% 1.71/0.63  fof(f65,plain,(
% 1.71/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.71/0.63    inference(cnf_transformation,[],[f5])).
% 1.71/0.63  fof(f5,axiom,(
% 1.71/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.71/0.63  fof(f1042,plain,(
% 1.71/0.63    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_16 | ~spl4_65 | spl4_67)),
% 1.71/0.63    inference(forward_demodulation,[],[f1037,f241])).
% 1.71/0.63  fof(f241,plain,(
% 1.71/0.63    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | ~spl4_16),
% 1.71/0.63    inference(avatar_component_clause,[],[f239])).
% 1.71/0.63  fof(f239,plain,(
% 1.71/0.63    spl4_16 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.71/0.63  fof(f1037,plain,(
% 1.71/0.63    ~m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_65 | spl4_67)),
% 1.71/0.63    inference(backward_demodulation,[],[f1008,f954])).
% 1.71/0.63  fof(f954,plain,(
% 1.71/0.63    ( ! [X4,X5,X3] : (k7_relat_1(k1_xboole_0,X5) = k2_partfun1(X3,X4,k1_xboole_0,X5)) ) | ~spl4_65),
% 1.71/0.63    inference(avatar_component_clause,[],[f953])).
% 1.71/0.63  fof(f953,plain,(
% 1.71/0.63    spl4_65 <=> ! [X3,X5,X4] : k7_relat_1(k1_xboole_0,X5) = k2_partfun1(X3,X4,k1_xboole_0,X5)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.71/0.63  fof(f1008,plain,(
% 1.71/0.63    ~m1_subset_1(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | spl4_67),
% 1.71/0.63    inference(avatar_component_clause,[],[f1006])).
% 1.71/0.63  fof(f1006,plain,(
% 1.71/0.63    spl4_67 <=> m1_subset_1(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.71/0.63  fof(f1009,plain,(
% 1.71/0.63    ~spl4_67 | ~spl4_8 | spl4_24 | ~spl4_51 | ~spl4_59),
% 1.71/0.63    inference(avatar_split_clause,[],[f966,f843,f756,f306,f142,f1006])).
% 1.71/0.63  fof(f142,plain,(
% 1.71/0.63    spl4_8 <=> k1_xboole_0 = sK0),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.71/0.63  fof(f756,plain,(
% 1.71/0.63    spl4_51 <=> k1_xboole_0 = sK2),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.71/0.63  fof(f843,plain,(
% 1.71/0.63    spl4_59 <=> k1_xboole_0 = sK3),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.71/0.63  fof(f966,plain,(
% 1.71/0.63    ~m1_subset_1(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl4_8 | spl4_24 | ~spl4_51 | ~spl4_59)),
% 1.71/0.63    inference(forward_demodulation,[],[f965,f144])).
% 1.71/0.63  fof(f144,plain,(
% 1.71/0.63    k1_xboole_0 = sK0 | ~spl4_8),
% 1.71/0.63    inference(avatar_component_clause,[],[f142])).
% 1.71/0.63  fof(f965,plain,(
% 1.71/0.63    ~m1_subset_1(k2_partfun1(sK0,sK1,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_24 | ~spl4_51 | ~spl4_59)),
% 1.71/0.63    inference(forward_demodulation,[],[f964,f845])).
% 1.71/0.63  fof(f845,plain,(
% 1.71/0.63    k1_xboole_0 = sK3 | ~spl4_59),
% 1.71/0.63    inference(avatar_component_clause,[],[f843])).
% 1.71/0.63  fof(f964,plain,(
% 1.71/0.63    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl4_24 | ~spl4_51)),
% 1.71/0.63    inference(forward_demodulation,[],[f963,f101])).
% 1.71/0.63  fof(f101,plain,(
% 1.71/0.63    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.71/0.63    inference(equality_resolution,[],[f80])).
% 1.71/0.63  fof(f80,plain,(
% 1.71/0.63    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.71/0.63    inference(cnf_transformation,[],[f54])).
% 1.71/0.63  fof(f54,plain,(
% 1.71/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.63    inference(flattening,[],[f53])).
% 1.71/0.63  fof(f53,plain,(
% 1.71/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.71/0.63    inference(nnf_transformation,[],[f4])).
% 1.71/0.63  fof(f4,axiom,(
% 1.71/0.63    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.71/0.63  fof(f963,plain,(
% 1.71/0.63    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (spl4_24 | ~spl4_51)),
% 1.71/0.63    inference(forward_demodulation,[],[f308,f758])).
% 1.71/0.63  fof(f758,plain,(
% 1.71/0.63    k1_xboole_0 = sK2 | ~spl4_51),
% 1.71/0.63    inference(avatar_component_clause,[],[f756])).
% 1.71/0.63  fof(f958,plain,(
% 1.71/0.63    ~spl4_16 | ~spl4_21 | ~spl4_60 | spl4_63),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f957])).
% 1.71/0.63  fof(f957,plain,(
% 1.71/0.63    $false | (~spl4_16 | ~spl4_21 | ~spl4_60 | spl4_63)),
% 1.71/0.63    inference(subsumption_resolution,[],[f956,f289])).
% 1.71/0.63  fof(f289,plain,(
% 1.71/0.63    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_21),
% 1.71/0.63    inference(avatar_component_clause,[],[f288])).
% 1.71/0.63  fof(f288,plain,(
% 1.71/0.63    spl4_21 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.71/0.63  fof(f956,plain,(
% 1.71/0.63    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (~spl4_16 | ~spl4_60 | spl4_63)),
% 1.71/0.63    inference(forward_demodulation,[],[f951,f241])).
% 1.71/0.63  fof(f951,plain,(
% 1.71/0.63    ~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) | (~spl4_60 | spl4_63)),
% 1.71/0.63    inference(backward_demodulation,[],[f884,f860])).
% 1.71/0.63  fof(f860,plain,(
% 1.71/0.63    ( ! [X4,X5,X3] : (k7_relat_1(k1_xboole_0,X5) = k2_partfun1(X3,X4,k1_xboole_0,X5)) ) | ~spl4_60),
% 1.71/0.63    inference(subsumption_resolution,[],[f855,f65])).
% 1.71/0.63  fof(f855,plain,(
% 1.71/0.63    ( ! [X4,X5,X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k7_relat_1(k1_xboole_0,X5) = k2_partfun1(X3,X4,k1_xboole_0,X5)) ) | ~spl4_60),
% 1.71/0.63    inference(resolution,[],[f852,f95])).
% 1.71/0.63  fof(f852,plain,(
% 1.71/0.63    v1_funct_1(k1_xboole_0) | ~spl4_60),
% 1.71/0.63    inference(avatar_component_clause,[],[f850])).
% 1.71/0.63  fof(f850,plain,(
% 1.71/0.63    spl4_60 <=> v1_funct_1(k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 1.71/0.63  fof(f884,plain,(
% 1.71/0.63    ~v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) | spl4_63),
% 1.71/0.63    inference(avatar_component_clause,[],[f882])).
% 1.71/0.63  fof(f882,plain,(
% 1.71/0.63    spl4_63 <=> v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 1.71/0.63  fof(f955,plain,(
% 1.71/0.63    spl4_65 | ~spl4_60),
% 1.71/0.63    inference(avatar_split_clause,[],[f860,f850,f953])).
% 1.71/0.63  fof(f885,plain,(
% 1.71/0.63    ~spl4_63 | ~spl4_52 | spl4_53),
% 1.71/0.63    inference(avatar_split_clause,[],[f840,f771,f766,f882])).
% 1.71/0.63  fof(f766,plain,(
% 1.71/0.63    spl4_52 <=> r1_tarski(sK3,k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.71/0.63  fof(f771,plain,(
% 1.71/0.63    spl4_53 <=> v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.71/0.63  fof(f840,plain,(
% 1.71/0.63    ~v1_funct_2(k2_partfun1(k1_xboole_0,sK1,k1_xboole_0,k1_xboole_0),k1_xboole_0,sK1) | (~spl4_52 | spl4_53)),
% 1.71/0.63    inference(backward_demodulation,[],[f773,f793])).
% 1.71/0.63  fof(f793,plain,(
% 1.71/0.63    k1_xboole_0 = sK3 | ~spl4_52),
% 1.71/0.63    inference(resolution,[],[f768,f180])).
% 1.71/0.63  fof(f180,plain,(
% 1.71/0.63    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.71/0.63    inference(resolution,[],[f76,f64])).
% 1.71/0.63  fof(f64,plain,(
% 1.71/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f3])).
% 1.71/0.63  fof(f3,axiom,(
% 1.71/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.71/0.63  fof(f76,plain,(
% 1.71/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.71/0.63    inference(cnf_transformation,[],[f51])).
% 1.71/0.63  fof(f51,plain,(
% 1.71/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.63    inference(flattening,[],[f50])).
% 1.71/0.63  fof(f50,plain,(
% 1.71/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.71/0.63    inference(nnf_transformation,[],[f1])).
% 1.71/0.63  fof(f1,axiom,(
% 1.71/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.71/0.63  fof(f768,plain,(
% 1.71/0.63    r1_tarski(sK3,k1_xboole_0) | ~spl4_52),
% 1.71/0.63    inference(avatar_component_clause,[],[f766])).
% 1.71/0.63  fof(f773,plain,(
% 1.71/0.63    ~v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) | spl4_53),
% 1.71/0.63    inference(avatar_component_clause,[],[f771])).
% 1.71/0.63  fof(f880,plain,(
% 1.71/0.63    spl4_59 | ~spl4_52),
% 1.71/0.63    inference(avatar_split_clause,[],[f798,f766,f843])).
% 1.71/0.63  fof(f798,plain,(
% 1.71/0.63    k1_xboole_0 = sK3 | ~spl4_52),
% 1.71/0.63    inference(subsumption_resolution,[],[f796,f64])).
% 1.71/0.63  fof(f796,plain,(
% 1.71/0.63    ~r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK3 | ~spl4_52),
% 1.71/0.63    inference(resolution,[],[f768,f76])).
% 1.71/0.63  fof(f853,plain,(
% 1.71/0.63    spl4_60 | ~spl4_1 | ~spl4_52),
% 1.71/0.63    inference(avatar_split_clause,[],[f833,f766,f108,f850])).
% 1.71/0.63  fof(f833,plain,(
% 1.71/0.63    v1_funct_1(k1_xboole_0) | (~spl4_1 | ~spl4_52)),
% 1.71/0.63    inference(backward_demodulation,[],[f110,f793])).
% 1.71/0.63  fof(f782,plain,(
% 1.71/0.63    spl4_52 | ~spl4_8 | ~spl4_9),
% 1.71/0.63    inference(avatar_split_clause,[],[f706,f150,f142,f766])).
% 1.71/0.63  fof(f150,plain,(
% 1.71/0.63    spl4_9 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.71/0.63  fof(f706,plain,(
% 1.71/0.63    r1_tarski(sK3,k1_xboole_0) | (~spl4_8 | ~spl4_9)),
% 1.71/0.63    inference(forward_demodulation,[],[f705,f101])).
% 1.71/0.63  fof(f705,plain,(
% 1.71/0.63    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl4_8 | ~spl4_9)),
% 1.71/0.63    inference(forward_demodulation,[],[f152,f144])).
% 1.71/0.63  fof(f152,plain,(
% 1.71/0.63    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_9),
% 1.71/0.63    inference(avatar_component_clause,[],[f150])).
% 1.71/0.63  fof(f774,plain,(
% 1.71/0.63    ~spl4_53 | ~spl4_8 | spl4_30),
% 1.71/0.63    inference(avatar_split_clause,[],[f701,f428,f142,f771])).
% 1.71/0.63  fof(f428,plain,(
% 1.71/0.63    spl4_30 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK0),sK0,sK1)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.71/0.63  fof(f701,plain,(
% 1.71/0.63    ~v1_funct_2(k2_partfun1(k1_xboole_0,sK1,sK3,k1_xboole_0),k1_xboole_0,sK1) | (~spl4_8 | spl4_30)),
% 1.71/0.63    inference(forward_demodulation,[],[f430,f144])).
% 1.71/0.63  fof(f430,plain,(
% 1.71/0.63    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK0),sK0,sK1) | spl4_30),
% 1.71/0.63    inference(avatar_component_clause,[],[f428])).
% 1.71/0.63  fof(f759,plain,(
% 1.71/0.63    spl4_51 | ~spl4_28),
% 1.71/0.63    inference(avatar_split_clause,[],[f686,f392,f756])).
% 1.71/0.63  fof(f392,plain,(
% 1.71/0.63    spl4_28 <=> r1_tarski(sK2,k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.71/0.63  fof(f686,plain,(
% 1.71/0.63    k1_xboole_0 = sK2 | ~spl4_28),
% 1.71/0.63    inference(subsumption_resolution,[],[f684,f64])).
% 1.71/0.63  fof(f684,plain,(
% 1.71/0.63    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2 | ~spl4_28),
% 1.71/0.63    inference(resolution,[],[f394,f76])).
% 1.71/0.63  fof(f394,plain,(
% 1.71/0.63    r1_tarski(sK2,k1_xboole_0) | ~spl4_28),
% 1.71/0.63    inference(avatar_component_clause,[],[f392])).
% 1.71/0.63  fof(f431,plain,(
% 1.71/0.63    ~spl4_30 | ~spl4_17 | spl4_23),
% 1.71/0.63    inference(avatar_split_clause,[],[f424,f302,f247,f428])).
% 1.71/0.63  fof(f247,plain,(
% 1.71/0.63    spl4_17 <=> sK0 = sK2),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.71/0.63  fof(f424,plain,(
% 1.71/0.63    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK0),sK0,sK1) | (~spl4_17 | spl4_23)),
% 1.71/0.63    inference(forward_demodulation,[],[f304,f249])).
% 1.71/0.63  fof(f249,plain,(
% 1.71/0.63    sK0 = sK2 | ~spl4_17),
% 1.71/0.63    inference(avatar_component_clause,[],[f247])).
% 1.71/0.63  fof(f395,plain,(
% 1.71/0.63    spl4_28 | ~spl4_2 | ~spl4_8),
% 1.71/0.63    inference(avatar_split_clause,[],[f387,f142,f113,f392])).
% 1.71/0.63  fof(f387,plain,(
% 1.71/0.63    r1_tarski(sK2,k1_xboole_0) | (~spl4_2 | ~spl4_8)),
% 1.71/0.63    inference(backward_demodulation,[],[f115,f144])).
% 1.71/0.63  fof(f345,plain,(
% 1.71/0.63    ~spl4_8 | spl4_18),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f344])).
% 1.71/0.63  fof(f344,plain,(
% 1.71/0.63    $false | (~spl4_8 | spl4_18)),
% 1.71/0.63    inference(subsumption_resolution,[],[f342,f64])).
% 1.71/0.63  fof(f342,plain,(
% 1.71/0.63    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_8 | spl4_18)),
% 1.71/0.63    inference(backward_demodulation,[],[f253,f144])).
% 1.71/0.63  fof(f253,plain,(
% 1.71/0.63    ~r1_tarski(sK0,sK2) | spl4_18),
% 1.71/0.63    inference(avatar_component_clause,[],[f251])).
% 1.71/0.63  fof(f251,plain,(
% 1.71/0.63    spl4_18 <=> r1_tarski(sK0,sK2)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.71/0.63  fof(f329,plain,(
% 1.71/0.63    spl4_26 | ~spl4_6 | ~spl4_25),
% 1.71/0.63    inference(avatar_split_clause,[],[f324,f318,f133,f326])).
% 1.71/0.63  fof(f318,plain,(
% 1.71/0.63    spl4_25 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.71/0.63  fof(f324,plain,(
% 1.71/0.63    sK0 = k1_relat_1(sK3) | (~spl4_6 | ~spl4_25)),
% 1.71/0.63    inference(forward_demodulation,[],[f225,f320])).
% 1.71/0.63  fof(f320,plain,(
% 1.71/0.63    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_25),
% 1.71/0.63    inference(avatar_component_clause,[],[f318])).
% 1.71/0.63  fof(f225,plain,(
% 1.71/0.63    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl4_6),
% 1.71/0.63    inference(resolution,[],[f84,f135])).
% 1.71/0.63  fof(f84,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f35])).
% 1.71/0.63  fof(f35,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(ennf_transformation,[],[f16])).
% 1.71/0.63  fof(f16,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.71/0.63  fof(f321,plain,(
% 1.71/0.63    spl4_25 | ~spl4_3 | ~spl4_6 | spl4_7),
% 1.71/0.63    inference(avatar_split_clause,[],[f286,f138,f133,f118,f318])).
% 1.71/0.63  fof(f118,plain,(
% 1.71/0.63    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.71/0.63  fof(f138,plain,(
% 1.71/0.63    spl4_7 <=> k1_xboole_0 = sK1),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.71/0.63  fof(f286,plain,(
% 1.71/0.63    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_3 | ~spl4_6 | spl4_7)),
% 1.71/0.63    inference(subsumption_resolution,[],[f285,f135])).
% 1.71/0.63  fof(f285,plain,(
% 1.71/0.63    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_3 | spl4_7)),
% 1.71/0.63    inference(subsumption_resolution,[],[f283,f140])).
% 1.71/0.63  fof(f140,plain,(
% 1.71/0.63    k1_xboole_0 != sK1 | spl4_7),
% 1.71/0.63    inference(avatar_component_clause,[],[f138])).
% 1.71/0.63  fof(f283,plain,(
% 1.71/0.63    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 1.71/0.63    inference(resolution,[],[f87,f120])).
% 1.71/0.63  fof(f120,plain,(
% 1.71/0.63    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 1.71/0.63    inference(avatar_component_clause,[],[f118])).
% 1.71/0.63  fof(f87,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.63    inference(cnf_transformation,[],[f55])).
% 1.71/0.63  fof(f55,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(nnf_transformation,[],[f38])).
% 1.71/0.63  fof(f38,plain,(
% 1.71/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(flattening,[],[f37])).
% 1.71/0.63  fof(f37,plain,(
% 1.71/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.63    inference(ennf_transformation,[],[f17])).
% 1.71/0.63  fof(f17,axiom,(
% 1.71/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.71/0.63  fof(f311,plain,(
% 1.71/0.63    ~spl4_1 | ~spl4_6 | spl4_22),
% 1.71/0.63    inference(avatar_contradiction_clause,[],[f310])).
% 1.71/0.63  fof(f310,plain,(
% 1.71/0.63    $false | (~spl4_1 | ~spl4_6 | spl4_22)),
% 1.71/0.63    inference(unit_resulting_resolution,[],[f110,f135,f300,f96])).
% 1.71/0.63  fof(f96,plain,(
% 1.71/0.63    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 1.71/0.63    inference(cnf_transformation,[],[f46])).
% 1.71/0.63  fof(f300,plain,(
% 1.71/0.63    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_22),
% 1.71/0.63    inference(avatar_component_clause,[],[f298])).
% 1.71/0.63  fof(f309,plain,(
% 1.71/0.63    ~spl4_22 | ~spl4_23 | ~spl4_24),
% 1.71/0.63    inference(avatar_split_clause,[],[f61,f306,f302,f298])).
% 1.71/0.63  fof(f61,plain,(
% 1.71/0.63    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 1.71/0.63    inference(cnf_transformation,[],[f48])).
% 1.71/0.63  fof(f48,plain,(
% 1.71/0.63    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.71/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f47])).
% 1.71/0.63  fof(f47,plain,(
% 1.71/0.63    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.71/0.63    introduced(choice_axiom,[])).
% 1.71/0.63  fof(f24,plain,(
% 1.71/0.63    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.71/0.63    inference(flattening,[],[f23])).
% 1.71/0.63  fof(f23,plain,(
% 1.71/0.63    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.71/0.63    inference(ennf_transformation,[],[f22])).
% 1.71/0.63  fof(f22,negated_conjecture,(
% 1.71/0.63    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.71/0.63    inference(negated_conjecture,[],[f21])).
% 1.71/0.63  fof(f21,conjecture,(
% 1.71/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 1.71/0.63  fof(f290,plain,(
% 1.71/0.63    spl4_21 | ~spl4_20),
% 1.71/0.63    inference(avatar_split_clause,[],[f282,f276,f288])).
% 1.71/0.63  fof(f276,plain,(
% 1.71/0.63    spl4_20 <=> ! [X1,X0] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.71/0.63  fof(f282,plain,(
% 1.71/0.63    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_20),
% 1.71/0.63    inference(subsumption_resolution,[],[f281,f65])).
% 1.71/0.63  fof(f281,plain,(
% 1.71/0.63    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_20),
% 1.71/0.63    inference(trivial_inequality_removal,[],[f280])).
% 1.71/0.63  fof(f280,plain,(
% 1.71/0.63    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_20),
% 1.71/0.63    inference(superposition,[],[f265,f277])).
% 1.71/0.63  fof(f277,plain,(
% 1.71/0.63    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl4_20),
% 1.71/0.63    inference(avatar_component_clause,[],[f276])).
% 1.71/0.63  fof(f265,plain,(
% 1.71/0.63    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 1.71/0.63    inference(forward_demodulation,[],[f105,f101])).
% 1.71/0.63  fof(f105,plain,(
% 1.71/0.63    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.71/0.63    inference(equality_resolution,[],[f90])).
% 1.71/0.63  fof(f90,plain,(
% 1.71/0.63    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.63    inference(cnf_transformation,[],[f55])).
% 1.71/0.63  fof(f278,plain,(
% 1.71/0.63    spl4_20 | ~spl4_4),
% 1.71/0.63    inference(avatar_split_clause,[],[f229,f123,f276])).
% 1.71/0.63  fof(f123,plain,(
% 1.71/0.63    spl4_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.71/0.63  fof(f229,plain,(
% 1.71/0.63    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | ~spl4_4),
% 1.71/0.63    inference(forward_demodulation,[],[f224,f125])).
% 1.71/0.63  fof(f125,plain,(
% 1.71/0.63    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_4),
% 1.71/0.63    inference(avatar_component_clause,[],[f123])).
% 1.71/0.63  fof(f224,plain,(
% 1.71/0.63    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 1.71/0.63    inference(resolution,[],[f84,f65])).
% 1.71/0.63  fof(f254,plain,(
% 1.71/0.63    spl4_17 | ~spl4_18 | ~spl4_2),
% 1.71/0.63    inference(avatar_split_clause,[],[f181,f113,f251,f247])).
% 1.71/0.63  fof(f181,plain,(
% 1.71/0.63    ~r1_tarski(sK0,sK2) | sK0 = sK2 | ~spl4_2),
% 1.71/0.63    inference(resolution,[],[f76,f115])).
% 1.71/0.63  fof(f242,plain,(
% 1.71/0.63    spl4_16 | ~spl4_4 | ~spl4_11),
% 1.71/0.63    inference(avatar_split_clause,[],[f178,f167,f123,f239])).
% 1.71/0.63  fof(f167,plain,(
% 1.71/0.63    spl4_11 <=> v1_relat_1(k1_xboole_0)),
% 1.71/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.71/0.63  fof(f178,plain,(
% 1.71/0.63    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | (~spl4_4 | ~spl4_11)),
% 1.71/0.63    inference(forward_demodulation,[],[f174,f125])).
% 1.71/0.63  fof(f174,plain,(
% 1.71/0.63    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~spl4_11),
% 1.71/0.63    inference(resolution,[],[f169,f66])).
% 1.71/0.63  fof(f66,plain,(
% 1.71/0.63    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 1.71/0.63    inference(cnf_transformation,[],[f25])).
% 1.71/0.63  fof(f25,plain,(
% 1.71/0.63    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.71/0.63    inference(ennf_transformation,[],[f12])).
% 1.71/0.63  fof(f12,axiom,(
% 1.71/0.63    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 1.71/0.63  fof(f169,plain,(
% 1.71/0.63    v1_relat_1(k1_xboole_0) | ~spl4_11),
% 1.71/0.63    inference(avatar_component_clause,[],[f167])).
% 1.71/0.63  fof(f170,plain,(
% 1.71/0.63    spl4_11),
% 1.71/0.63    inference(avatar_split_clause,[],[f154,f167])).
% 1.71/0.63  fof(f154,plain,(
% 1.71/0.63    v1_relat_1(k1_xboole_0)),
% 1.71/0.63    inference(resolution,[],[f83,f65])).
% 1.71/0.63  fof(f163,plain,(
% 1.71/0.63    spl4_10 | ~spl4_6),
% 1.71/0.63    inference(avatar_split_clause,[],[f155,f133,f160])).
% 1.71/0.63  fof(f155,plain,(
% 1.71/0.63    v1_relat_1(sK3) | ~spl4_6),
% 1.71/0.63    inference(resolution,[],[f83,f135])).
% 1.71/0.63  fof(f153,plain,(
% 1.71/0.63    spl4_9 | ~spl4_6),
% 1.71/0.63    inference(avatar_split_clause,[],[f147,f133,f150])).
% 1.71/0.63  fof(f147,plain,(
% 1.71/0.63    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_6),
% 1.71/0.63    inference(resolution,[],[f77,f135])).
% 1.71/0.63  fof(f77,plain,(
% 1.71/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.71/0.63    inference(cnf_transformation,[],[f52])).
% 1.71/0.63  fof(f52,plain,(
% 1.71/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.71/0.63    inference(nnf_transformation,[],[f6])).
% 1.71/0.63  fof(f6,axiom,(
% 1.71/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.71/0.63  fof(f145,plain,(
% 1.71/0.63    ~spl4_7 | spl4_8),
% 1.71/0.63    inference(avatar_split_clause,[],[f60,f142,f138])).
% 1.71/0.63  fof(f60,plain,(
% 1.71/0.63    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.71/0.63    inference(cnf_transformation,[],[f48])).
% 2.15/0.64  fof(f136,plain,(
% 2.15/0.64    spl4_6),
% 2.15/0.64    inference(avatar_split_clause,[],[f58,f133])).
% 2.15/0.64  fof(f58,plain,(
% 2.15/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.15/0.64    inference(cnf_transformation,[],[f48])).
% 2.15/0.64  fof(f126,plain,(
% 2.15/0.64    spl4_4),
% 2.15/0.64    inference(avatar_split_clause,[],[f62,f123])).
% 2.15/0.64  fof(f62,plain,(
% 2.15/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.15/0.64    inference(cnf_transformation,[],[f10])).
% 2.15/0.64  fof(f10,axiom,(
% 2.15/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.15/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.15/0.64  fof(f121,plain,(
% 2.15/0.64    spl4_3),
% 2.15/0.64    inference(avatar_split_clause,[],[f57,f118])).
% 2.15/0.64  fof(f57,plain,(
% 2.15/0.64    v1_funct_2(sK3,sK0,sK1)),
% 2.15/0.64    inference(cnf_transformation,[],[f48])).
% 2.15/0.64  fof(f116,plain,(
% 2.15/0.64    spl4_2),
% 2.15/0.64    inference(avatar_split_clause,[],[f59,f113])).
% 2.15/0.64  fof(f59,plain,(
% 2.15/0.64    r1_tarski(sK2,sK0)),
% 2.15/0.64    inference(cnf_transformation,[],[f48])).
% 2.15/0.64  fof(f111,plain,(
% 2.15/0.64    spl4_1),
% 2.15/0.64    inference(avatar_split_clause,[],[f56,f108])).
% 2.15/0.64  fof(f56,plain,(
% 2.15/0.64    v1_funct_1(sK3)),
% 2.15/0.64    inference(cnf_transformation,[],[f48])).
% 2.15/0.64  % SZS output end Proof for theBenchmark
% 2.15/0.64  % (28523)------------------------------
% 2.15/0.64  % (28523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.64  % (28523)Termination reason: Refutation
% 2.15/0.64  
% 2.15/0.64  % (28523)Memory used [KB]: 7419
% 2.15/0.64  % (28523)Time elapsed: 0.202 s
% 2.15/0.64  % (28523)------------------------------
% 2.15/0.64  % (28523)------------------------------
% 2.15/0.65  % (28520)Success in time 0.281 s
%------------------------------------------------------------------------------
