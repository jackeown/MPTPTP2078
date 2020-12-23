%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1107+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:07 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 100 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 ( 285 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2772,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2307,f2317,f2327,f2359,f2374,f2504,f2748,f2764])).

fof(f2764,plain,
    ( spl53_5
    | ~ spl53_12
    | ~ spl53_36 ),
    inference(avatar_contradiction_clause,[],[f2763])).

fof(f2763,plain,
    ( $false
    | spl53_5
    | ~ spl53_12
    | ~ spl53_36 ),
    inference(subsumption_resolution,[],[f2762,f2326])).

fof(f2326,plain,
    ( sK1 != u1_struct_0(k1_pre_topc(sK0,sK1))
    | spl53_5 ),
    inference(avatar_component_clause,[],[f2324])).

fof(f2324,plain,
    ( spl53_5
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl53_5])])).

fof(f2762,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl53_12
    | ~ spl53_36 ),
    inference(forward_demodulation,[],[f2761,f2373])).

fof(f2373,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl53_12 ),
    inference(avatar_component_clause,[],[f2371])).

fof(f2371,plain,
    ( spl53_12
  <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl53_12])])).

fof(f2761,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl53_36 ),
    inference(unit_resulting_resolution,[],[f2747,f2118])).

fof(f2118,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1839])).

fof(f1839,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1764])).

fof(f1764,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f2747,plain,
    ( l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl53_36 ),
    inference(avatar_component_clause,[],[f2745])).

fof(f2745,plain,
    ( spl53_36
  <=> l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl53_36])])).

fof(f2748,plain,
    ( spl53_36
    | ~ spl53_25 ),
    inference(avatar_split_clause,[],[f2520,f2501,f2745])).

fof(f2501,plain,
    ( spl53_25
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl53_25])])).

fof(f2520,plain,
    ( l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl53_25 ),
    inference(unit_resulting_resolution,[],[f2503,f2213])).

fof(f2213,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1920])).

fof(f1920,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1770])).

fof(f1770,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2503,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl53_25 ),
    inference(avatar_component_clause,[],[f2501])).

fof(f2504,plain,
    ( spl53_25
    | ~ spl53_1
    | ~ spl53_9 ),
    inference(avatar_split_clause,[],[f2405,f2356,f2304,f2501])).

fof(f2304,plain,
    ( spl53_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl53_1])])).

fof(f2356,plain,
    ( spl53_9
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl53_9])])).

fof(f2405,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl53_1
    | ~ spl53_9 ),
    inference(unit_resulting_resolution,[],[f2358,f2306,f2085])).

fof(f2085,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f1819])).

fof(f1819,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1772])).

fof(f1772,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f2306,plain,
    ( l1_pre_topc(sK0)
    | ~ spl53_1 ),
    inference(avatar_component_clause,[],[f2304])).

fof(f2358,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl53_9 ),
    inference(avatar_component_clause,[],[f2356])).

fof(f2374,plain,
    ( spl53_12
    | ~ spl53_1
    | ~ spl53_3 ),
    inference(avatar_split_clause,[],[f2351,f2314,f2304,f2371])).

fof(f2314,plain,
    ( spl53_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl53_3])])).

fof(f2351,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl53_1
    | ~ spl53_3 ),
    inference(unit_resulting_resolution,[],[f2306,f2316,f2302])).

fof(f2302,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f2301,f2062])).

fof(f2062,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1800])).

fof(f1800,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1799])).

fof(f1799,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1767])).

fof(f1767,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f2301,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f2261,f2063])).

fof(f2063,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1800])).

fof(f2261,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f2067])).

fof(f2067,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1963])).

fof(f1963,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1806])).

fof(f1806,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1805])).

fof(f1805,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1761])).

fof(f1761,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f2316,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl53_3 ),
    inference(avatar_component_clause,[],[f2314])).

fof(f2359,plain,
    ( spl53_9
    | ~ spl53_1
    | ~ spl53_3 ),
    inference(avatar_split_clause,[],[f2342,f2314,f2304,f2356])).

fof(f2342,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl53_1
    | ~ spl53_3 ),
    inference(unit_resulting_resolution,[],[f2306,f2316,f2063])).

fof(f2327,plain,(
    ~ spl53_5 ),
    inference(avatar_split_clause,[],[f2061,f2324])).

fof(f2061,plain,(
    sK1 != u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f1962])).

fof(f1962,plain,
    ( sK1 != u1_struct_0(k1_pre_topc(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1798,f1961,f1960])).

fof(f1960,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( u1_struct_0(k1_pre_topc(X0,X1)) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( u1_struct_0(k1_pre_topc(sK0,X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1961,plain,
    ( ? [X1] :
        ( u1_struct_0(k1_pre_topc(sK0,X1)) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( sK1 != u1_struct_0(k1_pre_topc(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f1798,plain,(
    ? [X0] :
      ( ? [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1793])).

fof(f1793,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f1792])).

fof(f1792,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f2317,plain,(
    spl53_3 ),
    inference(avatar_split_clause,[],[f2060,f2314])).

fof(f2060,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f1962])).

fof(f2307,plain,(
    spl53_1 ),
    inference(avatar_split_clause,[],[f2059,f2304])).

fof(f2059,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f1962])).
%------------------------------------------------------------------------------
