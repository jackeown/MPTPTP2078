%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1082+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 3.73s
% Output     : Refutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 115 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  227 ( 358 expanded)
%              Number of equality atoms :    2 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2042,f2048,f2073,f2097,f2186,f2332,f2361,f2382])).

fof(f2382,plain,
    ( spl34_2
    | spl34_5
    | ~ spl34_10
    | ~ spl34_16
    | ~ spl34_18 ),
    inference(avatar_contradiction_clause,[],[f2381])).

fof(f2381,plain,
    ( $false
    | spl34_2
    | spl34_5
    | ~ spl34_10
    | ~ spl34_16
    | ~ spl34_18 ),
    inference(subsumption_resolution,[],[f2380,f2067])).

fof(f2067,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | spl34_5 ),
    inference(avatar_component_clause,[],[f2066])).

fof(f2066,plain,
    ( spl34_5
  <=> v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_5])])).

fof(f2380,plain,
    ( v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | spl34_2
    | ~ spl34_10
    | ~ spl34_16
    | ~ spl34_18 ),
    inference(subsumption_resolution,[],[f2379,f2331])).

fof(f2331,plain,
    ( v1_funct_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | ~ spl34_16 ),
    inference(avatar_component_clause,[],[f2329])).

fof(f2329,plain,
    ( spl34_16
  <=> v1_funct_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_16])])).

fof(f2379,plain,
    ( ~ v1_funct_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | spl34_2
    | ~ spl34_10
    | ~ spl34_18 ),
    inference(subsumption_resolution,[],[f2378,f2047])).

fof(f2047,plain,
    ( ~ m1_funct_2(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),sK2,sK3)
    | spl34_2 ),
    inference(avatar_component_clause,[],[f2045])).

fof(f2045,plain,
    ( spl34_2
  <=> m1_funct_2(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_2])])).

fof(f2378,plain,
    ( m1_funct_2(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),sK2,sK3)
    | ~ v1_funct_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ spl34_10
    | ~ spl34_18 ),
    inference(subsumption_resolution,[],[f2372,f2189])).

fof(f2189,plain,
    ( m1_subset_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl34_10 ),
    inference(resolution,[],[f2185,f2020])).

fof(f2020,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f1874,f1878])).

fof(f1878,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f1597])).

fof(f1597,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).

fof(f1874,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1721])).

fof(f1721,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f1572])).

fof(f1572,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f2185,plain,
    ( r2_hidden(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ spl34_10 ),
    inference(avatar_component_clause,[],[f2183])).

fof(f2183,plain,
    ( spl34_10
  <=> r2_hidden(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_10])])).

fof(f2372,plain,
    ( ~ m1_subset_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | m1_funct_2(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),sK2,sK3)
    | ~ v1_funct_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ spl34_18 ),
    inference(resolution,[],[f2360,f1853])).

fof(f1853,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(sK4(X0,X1,X2))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f1794])).

fof(f1794,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ( ( ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
              | ~ v1_funct_1(sK4(X0,X1,X2)) )
            & m1_subset_1(sK4(X0,X1,X2),X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f1792,f1793])).

fof(f1793,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK4(X0,X1,X2),X0,X1)
          | ~ v1_funct_1(sK4(X0,X1,X2)) )
        & m1_subset_1(sK4(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f1792,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(rectify,[],[f1791])).

fof(f1791,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
              | ~ m1_subset_1(X3,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(nnf_transformation,[],[f1714])).

fof(f1714,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f1481])).

fof(f1481,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

fof(f2360,plain,
    ( v1_funct_2(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2,sK3)
    | ~ spl34_18 ),
    inference(avatar_component_clause,[],[f2358])).

fof(f2358,plain,
    ( spl34_18
  <=> v1_funct_2(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_18])])).

fof(f2361,plain,
    ( spl34_18
    | ~ spl34_10 ),
    inference(avatar_split_clause,[],[f2190,f2183,f2358])).

fof(f2190,plain,
    ( v1_funct_2(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),sK2,sK3)
    | ~ spl34_10 ),
    inference(resolution,[],[f2185,f2021])).

fof(f2021,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f1873,f1878])).

fof(f1873,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1721])).

fof(f2332,plain,
    ( spl34_16
    | ~ spl34_10 ),
    inference(avatar_split_clause,[],[f2191,f2183,f2329])).

fof(f2191,plain,
    ( v1_funct_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))))
    | ~ spl34_10 ),
    inference(resolution,[],[f2185,f2022])).

fof(f2022,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f1872,f1878])).

fof(f1872,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1721])).

fof(f2186,plain,
    ( spl34_10
    | spl34_5
    | ~ spl34_6 ),
    inference(avatar_split_clause,[],[f2115,f2070,f2066,f2183])).

fof(f2070,plain,
    ( spl34_6
  <=> m1_subset_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_6])])).

fof(f2115,plain,
    ( r2_hidden(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | spl34_5
    | ~ spl34_6 ),
    inference(subsumption_resolution,[],[f2112,f2067])).

fof(f2112,plain,
    ( r2_hidden(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ spl34_6 ),
    inference(resolution,[],[f2072,f1956])).

fof(f1956,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1827])).

fof(f1827,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1764])).

fof(f1764,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f2072,plain,
    ( m1_subset_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ spl34_6 ),
    inference(avatar_component_clause,[],[f2070])).

fof(f2097,plain,
    ( spl34_1
    | ~ spl34_5 ),
    inference(avatar_contradiction_clause,[],[f2096])).

fof(f2096,plain,
    ( $false
    | spl34_1
    | ~ spl34_5 ),
    inference(subsumption_resolution,[],[f2083,f2041])).

fof(f2041,plain,
    ( ~ v1_xboole_0(sK3)
    | spl34_1 ),
    inference(avatar_component_clause,[],[f2039])).

fof(f2039,plain,
    ( spl34_1
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_1])])).

fof(f2083,plain,
    ( v1_xboole_0(sK3)
    | ~ spl34_5 ),
    inference(resolution,[],[f2068,f2025])).

fof(f2025,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(definition_unfolding,[],[f1877,f1878])).

fof(f1877,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1726])).

fof(f1726,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1523])).

fof(f1523,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_funct_2)).

fof(f2068,plain,
    ( v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | ~ spl34_5 ),
    inference(avatar_component_clause,[],[f2066])).

fof(f2073,plain,
    ( spl34_5
    | spl34_6
    | spl34_2 ),
    inference(avatar_split_clause,[],[f2049,f2045,f2070,f2066])).

fof(f2049,plain,
    ( m1_subset_1(sK4(sK2,sK3,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))),k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))
    | spl34_2 ),
    inference(resolution,[],[f2047,f1852])).

fof(f1852,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X2,X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),X2)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f1794])).

fof(f2048,plain,(
    ~ spl34_2 ),
    inference(avatar_split_clause,[],[f2002,f2045])).

fof(f2002,plain,(
    ~ m1_funct_2(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)),sK2,sK3) ),
    inference(definition_unfolding,[],[f1845,f1878])).

fof(f1845,plain,(
    ~ m1_funct_2(k1_funct_2(sK2,sK3),sK2,sK3) ),
    inference(cnf_transformation,[],[f1790])).

fof(f1790,plain,
    ( ~ m1_funct_2(k1_funct_2(sK2,sK3),sK2,sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f1709,f1789])).

fof(f1789,plain,
    ( ? [X0,X1] :
        ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
        & ~ v1_xboole_0(X1) )
   => ( ~ m1_funct_2(k1_funct_2(sK2,sK3),sK2,sK3)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f1709,plain,(
    ? [X0,X1] :
      ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1644])).

fof(f1644,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    inference(negated_conjecture,[],[f1643])).

fof(f1643,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_funct_2)).

fof(f2042,plain,(
    ~ spl34_1 ),
    inference(avatar_split_clause,[],[f1844,f2039])).

fof(f1844,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f1790])).
%------------------------------------------------------------------------------
