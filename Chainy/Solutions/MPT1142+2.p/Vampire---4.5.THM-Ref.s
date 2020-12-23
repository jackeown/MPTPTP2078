%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1142+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:09 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 211 expanded)
%              Number of leaves         :   22 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :  349 (1655 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1945,f1952,f1956,f1960,f1961,f1965,f1969,f1973,f1977,f1981,f1985,f2093,f2098,f2105,f2106,f2107])).

% (2507)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% (2506)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
fof(f2107,plain,
    ( sK1 != sK2
    | r2_orders_2(sK0,sK1,sK3)
    | ~ r2_orders_2(sK0,sK2,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2106,plain,
    ( sK2 != sK3
    | r2_orders_2(sK0,sK1,sK3)
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2105,plain,
    ( spl6_3
    | spl6_21
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f2101,f1975,f1967,f1963,f1947,f2103,f1950])).

fof(f1950,plain,
    ( spl6_3
  <=> r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f2103,plain,
    ( spl6_21
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1947,plain,
    ( spl6_2
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1963,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1967,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f1975,plain,
    ( spl6_9
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f2101,plain,
    ( sK2 = sK3
    | r2_orders_2(sK0,sK2,sK3)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f2099,f1968])).

fof(f1968,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f1967])).

fof(f2099,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_orders_2(sK0,sK2,sK3)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(resolution,[],[f1948,f2058])).

fof(f2058,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK3)
        | sK3 = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,sK3) )
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(resolution,[],[f2026,f1964])).

fof(f1964,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f1963])).

fof(f2026,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | X0 = X1
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,X1) )
    | ~ spl6_9 ),
    inference(resolution,[],[f1931,f1976])).

fof(f1976,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f1975])).

fof(f1931,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1907])).

fof(f1907,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f1906])).

fof(f1906,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f1892])).

fof(f1892,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1861])).

fof(f1861,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f1948,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f1947])).

fof(f2098,plain,
    ( spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f2095])).

fof(f2095,plain,
    ( $false
    | spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f1984,f1980,f1976,f1944,f1951,f1964,f1972,f1968,f1955,f1936])).

fof(f1936,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X3)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_orders_2(X0,X1,X3)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f1898])).

fof(f1898,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f1897])).

fof(f1897,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ~ r2_orders_2(X0,X2,X3)
                  | ~ r2_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1878])).

fof(f1878,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r2_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_orders_2)).

fof(f1955,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f1954])).

fof(f1954,plain,
    ( spl6_4
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1972,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f1971])).

fof(f1971,plain,
    ( spl6_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f1951,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f1950])).

fof(f1944,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f1943])).

fof(f1943,plain,
    ( spl6_1
  <=> r2_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1980,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f1979])).

fof(f1979,plain,
    ( spl6_10
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1984,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f1983])).

fof(f1983,plain,
    ( spl6_11
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f2093,plain,
    ( spl6_4
    | spl6_20
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f2089,f1975,f1971,f1967,f1958,f2091,f1954])).

fof(f2091,plain,
    ( spl6_20
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f1958,plain,
    ( spl6_5
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2089,plain,
    ( sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f2086,f1972])).

fof(f2086,plain,
    ( sK1 = sK2
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f2059,f1959])).

fof(f1959,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f1958])).

fof(f2059,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,X1,sK2)
        | sK2 = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_orders_2(sK0,X1,sK2) )
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f2026,f1968])).

fof(f1985,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f1913,f1983])).

fof(f1913,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1904,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    & ( ( r2_orders_2(sK0,sK2,sK3)
        & r1_orders_2(sK0,sK1,sK2) )
      | ( r1_orders_2(sK0,sK2,sK3)
        & r2_orders_2(sK0,sK1,sK2) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1884,f1903,f1902,f1901,f1900])).

fof(f1900,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_orders_2(X0,X1,X3)
                    & ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(sK0,X1,X3)
                  & ( ( r2_orders_2(sK0,X2,X3)
                      & r1_orders_2(sK0,X1,X2) )
                    | ( r1_orders_2(sK0,X2,X3)
                      & r2_orders_2(sK0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1901,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_orders_2(sK0,X1,X3)
                & ( ( r2_orders_2(sK0,X2,X3)
                    & r1_orders_2(sK0,X1,X2) )
                  | ( r1_orders_2(sK0,X2,X3)
                    & r2_orders_2(sK0,X1,X2) ) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_orders_2(sK0,sK1,X3)
              & ( ( r2_orders_2(sK0,X2,X3)
                  & r1_orders_2(sK0,sK1,X2) )
                | ( r1_orders_2(sK0,X2,X3)
                  & r2_orders_2(sK0,sK1,X2) ) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1902,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_orders_2(sK0,sK1,X3)
            & ( ( r2_orders_2(sK0,X2,X3)
                & r1_orders_2(sK0,sK1,X2) )
              | ( r1_orders_2(sK0,X2,X3)
                & r2_orders_2(sK0,sK1,X2) ) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r2_orders_2(sK0,sK1,X3)
          & ( ( r2_orders_2(sK0,sK2,X3)
              & r1_orders_2(sK0,sK1,sK2) )
            | ( r1_orders_2(sK0,sK2,X3)
              & r2_orders_2(sK0,sK1,sK2) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1903,plain,
    ( ? [X3] :
        ( ~ r2_orders_2(sK0,sK1,X3)
        & ( ( r2_orders_2(sK0,sK2,X3)
            & r1_orders_2(sK0,sK1,sK2) )
          | ( r1_orders_2(sK0,sK2,X3)
            & r2_orders_2(sK0,sK1,sK2) ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_orders_2(sK0,sK1,sK3)
      & ( ( r2_orders_2(sK0,sK2,sK3)
          & r1_orders_2(sK0,sK1,sK2) )
        | ( r1_orders_2(sK0,sK2,sK3)
          & r2_orders_2(sK0,sK1,sK2) ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f1884,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f1883])).

fof(f1883,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1881])).

fof(f1881,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r2_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X2) )
                        | ( r1_orders_2(X0,X2,X3)
                          & r2_orders_2(X0,X1,X2) ) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1880])).

fof(f1880,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

fof(f1981,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f1914,f1979])).

fof(f1914,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1977,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f1915,f1975])).

fof(f1915,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1973,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f1916,f1971])).

fof(f1916,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1969,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f1917,f1967])).

fof(f1917,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1965,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f1918,f1963])).

fof(f1918,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1961,plain,
    ( spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f1919,f1958,f1954])).

fof(f1919,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1960,plain,
    ( spl6_2
    | spl6_5 ),
    inference(avatar_split_clause,[],[f1920,f1958,f1947])).

fof(f1920,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1956,plain,
    ( spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f1921,f1950,f1954])).

fof(f1921,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1952,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f1922,f1950,f1947])).

fof(f1922,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f1904])).

fof(f1945,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f1923,f1943])).

fof(f1923,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f1904])).
%------------------------------------------------------------------------------
