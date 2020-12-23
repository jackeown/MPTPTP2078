%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t65_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:47 EDT 2019

% Result     : Theorem 13.88s
% Output     : Refutation 13.88s
% Verified   : 
% Statistics : Number of formulae       :  534 (1501 expanded)
%              Number of leaves         :   98 ( 666 expanded)
%              Depth                    :   16
%              Number of atoms          : 3090 (9609 expanded)
%              Number of equality atoms :  155 ( 654 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128907,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f170,f177,f184,f191,f212,f219,f226,f233,f240,f255,f267,f299,f346,f509,f531,f549,f563,f608,f620,f646,f847,f897,f953,f960,f1084,f1103,f1199,f1221,f1805,f1861,f1951,f2042,f2134,f2140,f2196,f2257,f2371,f2373,f2487,f3114,f11012,f11030,f12471,f15096,f15352,f15357,f15425,f15653,f15796,f16240,f16401,f16485,f16566,f16596,f16989,f17785,f17786,f18831,f19452,f32795,f33066,f43132,f47094,f49310,f49313,f49646,f123490,f123525,f123856,f125160,f125407,f125468,f125753,f127771,f128891])).

fof(f128891,plain,
    ( ~ spl13_26
    | spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1934
    | ~ spl13_3324 ),
    inference(avatar_contradiction_clause,[],[f128886])).

fof(f128886,plain,
    ( $false
    | ~ spl13_26
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1934
    | ~ spl13_3324 ),
    inference(unit_resulting_resolution,[],[f266,f292,f345,f15336,f16397,f43126,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( sK3(X0,X1,X2) != X2
                  & ! [X4] :
                      ( r1_orders_2(X0,sK3(X0,X1,X2),X4)
                      | ~ r2_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X7] :
                  ( sK5(X0,X1) = X7
                  | ( ~ r1_orders_2(X0,X7,sK6(X0,X1,X7))
                    & r2_lattice3(X0,X1,sK6(X0,X1,X7))
                    & m1_subset_1(sK6(X0,X1,X7),u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X7)
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X9] :
                  ( r1_orders_2(X0,sK5(X0,X1),X9)
                  | ~ r2_lattice3(X0,X1,X9)
                  | ~ m1_subset_1(X9,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK5(X0,X1))
              & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f73,f77,f76,f75,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X3,X4)
              | ~ r2_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK3(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,sK3(X0,X1,X2),X4)
            | ~ r2_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X2,X5)
          & r2_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( X6 = X7
              | ? [X8] :
                  ( ~ r1_orders_2(X0,X7,X8)
                  & r2_lattice3(X0,X1,X8)
                  & m1_subset_1(X8,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X6,X9)
              | ~ r2_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ! [X7] :
            ( sK5(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X7,X8)
                & r2_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r2_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,sK5(X0,X1),X9)
            | ~ r2_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK5(X0,X1))
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X7,X8)
          & r2_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X7,sK6(X0,X1,X7))
        & r2_lattice3(X0,X1,sK6(X0,X1,X7))
        & m1_subset_1(sK6(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r2_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X2,X5)
                    & r2_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X6] :
                ( ! [X7] :
                    ( X6 = X7
                    | ? [X8] :
                        ( ~ r1_orders_2(X0,X7,X8)
                        & r2_lattice3(X0,X1,X8)
                        & m1_subset_1(X8,u1_struct_0(X0)) )
                    | ~ r2_lattice3(X0,X1,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                & ! [X9] :
                    ( r1_orders_2(X0,X6,X9)
                    | ~ r2_lattice3(X0,X1,X9)
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X6)
                & m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X3,X4)
                        | ~ r2_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X2,X5)
                    & r2_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( X2 = X3
                    | ? [X4] :
                        ( ~ r1_orders_2(X0,X3,X4)
                        & r2_lattice3(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X5] :
                    ( r1_orders_2(X0,X2,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r2_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X2,X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X2,X5) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r2_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X3,X4) ) )
                      & r2_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',d7_yellow_0)).

fof(f43126,plain,
    ( r1_orders_2(sK1,k1_yellow_0(sK0,sK2),sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_3324 ),
    inference(avatar_component_clause,[],[f43125])).

fof(f43125,plain,
    ( spl13_3324
  <=> r1_orders_2(sK1,k1_yellow_0(sK0,sK2),sK4(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3324])])).

fof(f16397,plain,
    ( k1_yellow_0(sK0,sK2) = sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_1934 ),
    inference(avatar_component_clause,[],[f16396])).

fof(f16396,plain,
    ( spl13_1934
  <=> k1_yellow_0(sK0,sK2) = sK3(sK1,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1934])])).

fof(f15336,plain,
    ( r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_1852 ),
    inference(avatar_component_clause,[],[f15335])).

fof(f15335,plain,
    ( spl13_1852
  <=> r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1852])])).

fof(f345,plain,
    ( m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_44 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl13_44
  <=> m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f292,plain,
    ( ~ r1_yellow_0(sK1,sK2)
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl13_33
  <=> ~ r1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f266,plain,
    ( l1_orders_2(sK1)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl13_26
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f127771,plain,
    ( spl13_3322
    | ~ spl13_288
    | ~ spl13_1876
    | ~ spl13_1916 ),
    inference(avatar_split_clause,[],[f126630,f16195,f15788,f1859,f43080])).

fof(f43080,plain,
    ( spl13_3322
  <=> r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK4(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3322])])).

fof(f1859,plain,
    ( spl13_288
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_288])])).

fof(f15788,plain,
    ( spl13_1876
  <=> r2_lattice3(sK0,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1876])])).

fof(f16195,plain,
    ( spl13_1916
  <=> m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1916])])).

fof(f126630,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_288
    | ~ spl13_1876
    | ~ spl13_1916 ),
    inference(subsumption_resolution,[],[f126474,f16196])).

fof(f16196,plain,
    ( m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_1916 ),
    inference(avatar_component_clause,[],[f16195])).

fof(f126474,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_288
    | ~ spl13_1876 ),
    inference(resolution,[],[f15789,f1860])).

fof(f1860,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0) )
    | ~ spl13_288 ),
    inference(avatar_component_clause,[],[f1859])).

fof(f15789,plain,
    ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_1876 ),
    inference(avatar_component_clause,[],[f15788])).

fof(f125753,plain,
    ( ~ spl13_26
    | spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1934
    | spl13_1957 ),
    inference(avatar_contradiction_clause,[],[f125752])).

fof(f125752,plain,
    ( $false
    | ~ spl13_26
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1934
    | ~ spl13_1957 ),
    inference(subsumption_resolution,[],[f125751,f266])).

fof(f125751,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1934
    | ~ spl13_1957 ),
    inference(subsumption_resolution,[],[f125750,f345])).

fof(f125750,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_1852
    | ~ spl13_1934
    | ~ spl13_1957 ),
    inference(subsumption_resolution,[],[f125749,f15336])).

fof(f125749,plain,
    ( ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_1934
    | ~ spl13_1957 ),
    inference(subsumption_resolution,[],[f125748,f16481])).

fof(f16481,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_1957 ),
    inference(avatar_component_clause,[],[f16480])).

fof(f16480,plain,
    ( spl13_1957
  <=> ~ r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1957])])).

fof(f125748,plain,
    ( r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_1934 ),
    inference(subsumption_resolution,[],[f125679,f292])).

fof(f125679,plain,
    ( r1_yellow_0(sK1,sK2)
    | r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_1934 ),
    inference(trivial_inequality_removal,[],[f125667])).

fof(f125667,plain,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK0,sK2)
    | r1_yellow_0(sK1,sK2)
    | r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_1934 ),
    inference(superposition,[],[f124,f16397])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f125468,plain,
    ( spl13_1964
    | ~ spl13_98
    | ~ spl13_1878
    | ~ spl13_1954 ),
    inference(avatar_split_clause,[],[f125466,f16477,f15794,f618,f16564])).

fof(f16564,plain,
    ( spl13_1964
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X1)
        | ~ r2_lattice3(sK1,sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1964])])).

fof(f618,plain,
    ( spl13_98
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_98])])).

fof(f15794,plain,
    ( spl13_1878
  <=> m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1878])])).

fof(f16477,plain,
    ( spl13_1954
  <=> ! [X0] :
        ( r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1954])])).

fof(f125466,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0)
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0) )
    | ~ spl13_98
    | ~ spl13_1878
    | ~ spl13_1954 ),
    inference(subsumption_resolution,[],[f123944,f15795])).

fof(f15795,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_1878 ),
    inference(avatar_component_clause,[],[f15794])).

fof(f123944,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0) )
    | ~ spl13_98
    | ~ spl13_1954 ),
    inference(duplicate_literal_removal,[],[f123935])).

fof(f123935,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0) )
    | ~ spl13_98
    | ~ spl13_1954 ),
    inference(resolution,[],[f16478,f619])).

fof(f619,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl13_98 ),
    inference(avatar_component_clause,[],[f618])).

fof(f16478,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0) )
    | ~ spl13_1954 ),
    inference(avatar_component_clause,[],[f16477])).

fof(f125407,plain,
    ( spl13_1926
    | ~ spl13_72
    | ~ spl13_1878 ),
    inference(avatar_split_clause,[],[f124526,f15794,f507,f16279])).

fof(f16279,plain,
    ( spl13_1926
  <=> m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1926])])).

fof(f507,plain,
    ( spl13_72
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f124526,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_72
    | ~ spl13_1878 ),
    inference(resolution,[],[f15795,f508])).

fof(f508,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f507])).

fof(f125160,plain,
    ( spl13_1928
    | ~ spl13_126
    | ~ spl13_1878
    | ~ spl13_2178 ),
    inference(avatar_split_clause,[],[f124741,f18018,f15794,f845,f16286])).

fof(f16286,plain,
    ( spl13_1928
  <=> r2_lattice3(sK0,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1928])])).

fof(f845,plain,
    ( spl13_126
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(sK0,sK2,X0)
        | ~ r2_lattice3(sK1,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_126])])).

fof(f18018,plain,
    ( spl13_2178
  <=> r2_lattice3(sK1,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2178])])).

fof(f124741,plain,
    ( r2_lattice3(sK0,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_126
    | ~ spl13_1878
    | ~ spl13_2178 ),
    inference(subsumption_resolution,[],[f124535,f15795])).

fof(f124535,plain,
    ( r2_lattice3(sK0,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_126
    | ~ spl13_2178 ),
    inference(resolution,[],[f18019,f846])).

fof(f846,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK1,sK2,X0)
        | r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_126 ),
    inference(avatar_component_clause,[],[f845])).

fof(f18019,plain,
    ( r2_lattice3(sK1,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_2178 ),
    inference(avatar_component_clause,[],[f18018])).

fof(f123856,plain,
    ( spl13_1934
    | ~ spl13_346
    | ~ spl13_1926
    | ~ spl13_1928
    | ~ spl13_7424 ),
    inference(avatar_split_clause,[],[f123537,f123523,f16286,f16279,f2255,f16396])).

fof(f2255,plain,
    ( spl13_346
  <=> ! [X0] :
        ( k1_yellow_0(sK0,sK2) = X0
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK2,X0))
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_346])])).

fof(f123523,plain,
    ( spl13_7424
  <=> ! [X0] :
        ( k1_yellow_0(sK0,sK2) = X0
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X0))
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7424])])).

fof(f123537,plain,
    ( k1_yellow_0(sK0,sK2) = sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_346
    | ~ spl13_1926
    | ~ spl13_1928
    | ~ spl13_7424 ),
    inference(subsumption_resolution,[],[f123536,f16280])).

fof(f16280,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_1926 ),
    inference(avatar_component_clause,[],[f16279])).

fof(f123536,plain,
    ( k1_yellow_0(sK0,sK2) = sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_346
    | ~ spl13_1928
    | ~ spl13_7424 ),
    inference(subsumption_resolution,[],[f123529,f16287])).

fof(f16287,plain,
    ( r2_lattice3(sK0,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_1928 ),
    inference(avatar_component_clause,[],[f16286])).

fof(f123529,plain,
    ( k1_yellow_0(sK0,sK2) = sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ r2_lattice3(sK0,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_346
    | ~ spl13_7424 ),
    inference(duplicate_literal_removal,[],[f123526])).

fof(f123526,plain,
    ( k1_yellow_0(sK0,sK2) = sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ r2_lattice3(sK0,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | k1_yellow_0(sK0,sK2) = sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ r2_lattice3(sK0,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_346
    | ~ spl13_7424 ),
    inference(resolution,[],[f123524,f2256])).

fof(f2256,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,sK2,X0))
        | k1_yellow_0(sK0,sK2) = X0
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_346 ),
    inference(avatar_component_clause,[],[f2255])).

fof(f123524,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X0))
        | k1_yellow_0(sK0,sK2) = X0
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_7424 ),
    inference(avatar_component_clause,[],[f123523])).

fof(f123525,plain,
    ( spl13_7424
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_324
    | ~ spl13_7412 ),
    inference(avatar_split_clause,[],[f123521,f123488,f2040,f224,f182,f123523])).

fof(f182,plain,
    ( spl13_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f224,plain,
    ( spl13_16
  <=> r1_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f2040,plain,
    ( spl13_324
  <=> k1_yellow_0(sK0,sK2) = sK5(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_324])])).

fof(f123488,plain,
    ( spl13_7412
  <=> ! [X3] :
        ( k1_yellow_0(sK0,sK2) = X3
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X3))
        | ~ m1_subset_1(sK6(sK0,sK2,X3),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7412])])).

fof(f123521,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,sK2) = X0
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X0))
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_324
    | ~ spl13_7412 ),
    inference(duplicate_literal_removal,[],[f123520])).

fof(f123520,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,sK2) = X0
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X0))
        | k1_yellow_0(sK0,sK2) = X0
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_324
    | ~ spl13_7412 ),
    inference(forward_demodulation,[],[f123519,f2041])).

fof(f2041,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ spl13_324 ),
    inference(avatar_component_clause,[],[f2040])).

fof(f123519,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X0))
        | k1_yellow_0(sK0,sK2) = X0
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK2) = X0 )
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_7412 ),
    inference(subsumption_resolution,[],[f123518,f183])).

fof(f183,plain,
    ( l1_orders_2(sK0)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f182])).

fof(f123518,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X0))
        | k1_yellow_0(sK0,sK2) = X0
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK2) = X0
        | ~ l1_orders_2(sK0) )
    | ~ spl13_16
    | ~ spl13_7412 ),
    inference(subsumption_resolution,[],[f123517,f225])).

fof(f225,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f224])).

fof(f123517,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X0))
        | k1_yellow_0(sK0,sK2) = X0
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK2) = X0
        | ~ r1_yellow_0(sK0,sK2)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_7412 ),
    inference(duplicate_literal_removal,[],[f123515])).

fof(f123515,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X0))
        | k1_yellow_0(sK0,sK2) = X0
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK2) = X0
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,sK2)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_7412 ),
    inference(resolution,[],[f123489,f111])).

fof(f111,plain,(
    ! [X0,X7,X1] :
      ( m1_subset_1(sK6(X0,X1,X7),u1_struct_0(X0))
      | sK5(X0,X1) = X7
      | ~ r2_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f123489,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK6(sK0,sK2,X3),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X3))
        | k1_yellow_0(sK0,sK2) = X3
        | ~ r2_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_7412 ),
    inference(avatar_component_clause,[],[f123488])).

fof(f123490,plain,
    ( spl13_7412
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_324
    | ~ spl13_2012 ),
    inference(avatar_split_clause,[],[f51262,f16987,f2040,f224,f182,f123488])).

fof(f16987,plain,
    ( spl13_2012
  <=> ! [X0] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2012])])).

fof(f51262,plain,
    ( ! [X3] :
        ( k1_yellow_0(sK0,sK2) = X3
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X3))
        | ~ m1_subset_1(sK6(sK0,sK2,X3),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_324
    | ~ spl13_2012 ),
    inference(forward_demodulation,[],[f51261,f2041])).

fof(f51261,plain,
    ( ! [X3] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X3))
        | ~ m1_subset_1(sK6(sK0,sK2,X3),u1_struct_0(sK0))
        | sK5(sK0,sK2) = X3
        | ~ r2_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_2012 ),
    inference(subsumption_resolution,[],[f51260,f183])).

fof(f51260,plain,
    ( ! [X3] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X3))
        | ~ m1_subset_1(sK6(sK0,sK2,X3),u1_struct_0(sK0))
        | sK5(sK0,sK2) = X3
        | ~ r2_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_16
    | ~ spl13_2012 ),
    inference(subsumption_resolution,[],[f51252,f225])).

fof(f51252,plain,
    ( ! [X3] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),sK6(sK0,sK2,X3))
        | ~ m1_subset_1(sK6(sK0,sK2,X3),u1_struct_0(sK0))
        | sK5(sK0,sK2) = X3
        | ~ r2_lattice3(sK0,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,sK2)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_2012 ),
    inference(resolution,[],[f16988,f112])).

fof(f112,plain,(
    ! [X0,X7,X1] :
      ( r2_lattice3(X0,X1,sK6(X0,X1,X7))
      | sK5(X0,X1) = X7
      | ~ r2_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f16988,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_2012 ),
    inference(avatar_component_clause,[],[f16987])).

fof(f49646,plain,
    ( spl13_1876
    | ~ spl13_126
    | ~ spl13_1916
    | ~ spl13_1956 ),
    inference(avatar_split_clause,[],[f49228,f16483,f16195,f845,f15788])).

fof(f16483,plain,
    ( spl13_1956
  <=> r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1956])])).

fof(f49228,plain,
    ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_126
    | ~ spl13_1916
    | ~ spl13_1956 ),
    inference(subsumption_resolution,[],[f46560,f16196])).

fof(f46560,plain,
    ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_126
    | ~ spl13_1956 ),
    inference(resolution,[],[f16484,f846])).

fof(f16484,plain,
    ( r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_1956 ),
    inference(avatar_component_clause,[],[f16483])).

fof(f49313,plain,
    ( spl13_1
    | ~ spl13_4
    | spl13_7
    | ~ spl13_14
    | ~ spl13_18
    | spl13_1877
    | ~ spl13_1916
    | ~ spl13_1956 ),
    inference(avatar_contradiction_clause,[],[f49309])).

fof(f49309,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_14
    | ~ spl13_18
    | ~ spl13_1877
    | ~ spl13_1916
    | ~ spl13_1956 ),
    inference(unit_resulting_resolution,[],[f169,f183,f190,f218,f232,f16196,f16484,f15786,f436])).

fof(f436,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r2_lattice3(X0,X2,X4)
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f160,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t59_yellow_0)).

fof(f160,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_lattice3(X0,X2,X4)
      | ~ r2_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X1,X2,X4)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_lattice3(X0,X2,X3)
                          | ~ r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                          | ~ r1_lattice3(X1,X2,X4) ) )
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_lattice3(X0,X2,X3)
                          | ~ r2_lattice3(X1,X2,X4) )
                        & ( r1_lattice3(X0,X2,X3)
                          | ~ r1_lattice3(X1,X2,X4) ) )
                      | X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r2_lattice3(X1,X2,X4)
                           => r2_lattice3(X0,X2,X3) )
                          & ( r1_lattice3(X1,X2,X4)
                           => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t63_yellow_0)).

fof(f15786,plain,
    ( ~ r2_lattice3(sK0,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_1877 ),
    inference(avatar_component_clause,[],[f15785])).

fof(f15785,plain,
    ( spl13_1877
  <=> ~ r2_lattice3(sK0,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1877])])).

fof(f232,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl13_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f218,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl13_14
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f190,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl13_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f169,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl13_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f49310,plain,
    ( ~ spl13_44
    | ~ spl13_370
    | ~ spl13_1852
    | spl13_1877
    | ~ spl13_1916
    | spl13_2179 ),
    inference(avatar_contradiction_clause,[],[f49306])).

fof(f49306,plain,
    ( $false
    | ~ spl13_44
    | ~ spl13_370
    | ~ spl13_1852
    | ~ spl13_1877
    | ~ spl13_1916
    | ~ spl13_2179 ),
    inference(unit_resulting_resolution,[],[f345,f15336,f18016,f16196,f15786,f2354])).

fof(f2354,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK4(sK1,sK2,X2),u1_struct_0(sK1))
        | r2_lattice3(sK0,sK2,sK4(sK1,sK2,X2))
        | r2_lattice3(sK1,sK2,sK3(sK1,sK2,X2))
        | ~ r2_lattice3(sK1,sK2,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl13_370 ),
    inference(avatar_component_clause,[],[f2353])).

fof(f2353,plain,
    ( spl13_370
  <=> ! [X2] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X2))
        | ~ m1_subset_1(sK4(sK1,sK2,X2),u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,sK3(sK1,sK2,X2))
        | ~ r2_lattice3(sK1,sK2,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_370])])).

fof(f18016,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_2179 ),
    inference(avatar_component_clause,[],[f18015])).

fof(f18015,plain,
    ( spl13_2179
  <=> ~ r2_lattice3(sK1,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2179])])).

fof(f47094,plain,
    ( spl13_1954
    | spl13_33
    | ~ spl13_1852
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2172 ),
    inference(avatar_split_clause,[],[f32789,f17996,f16195,f15788,f15335,f291,f16477])).

fof(f17996,plain,
    ( spl13_2172
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(sK4(sK1,X1,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X1,k1_yellow_0(sK0,sK2)))
        | r1_orders_2(sK1,sK3(sK1,X1,k1_yellow_0(sK0,sK2)),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_yellow_0(sK1,X1)
        | ~ r2_lattice3(sK1,X1,k1_yellow_0(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2172])])).

fof(f32789,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_33
    | ~ spl13_1852
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2172 ),
    inference(subsumption_resolution,[],[f32788,f15336])).

fof(f32788,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_33
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2172 ),
    inference(subsumption_resolution,[],[f32787,f292])).

fof(f32787,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_yellow_0(sK1,sK2)
        | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2172 ),
    inference(subsumption_resolution,[],[f32786,f16196])).

fof(f32786,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_yellow_0(sK1,sK2)
        | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_1876
    | ~ spl13_2172 ),
    inference(resolution,[],[f17997,f15789])).

fof(f17997,plain,
    ( ! [X2,X1] :
        ( ~ r2_lattice3(sK0,sK2,sK4(sK1,X1,k1_yellow_0(sK0,sK2)))
        | ~ m1_subset_1(sK4(sK1,X1,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r1_orders_2(sK1,sK3(sK1,X1,k1_yellow_0(sK0,sK2)),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_yellow_0(sK1,X1)
        | ~ r2_lattice3(sK1,X1,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_2172 ),
    inference(avatar_component_clause,[],[f17996])).

fof(f43132,plain,
    ( spl13_3324
    | ~ spl13_44
    | ~ spl13_144
    | ~ spl13_1916
    | ~ spl13_3322 ),
    inference(avatar_split_clause,[],[f43088,f43080,f16195,f951,f344,f43125])).

fof(f951,plain,
    ( spl13_144
  <=> ! [X1,X2] :
        ( ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_orders_2(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_144])])).

fof(f43088,plain,
    ( r1_orders_2(sK1,k1_yellow_0(sK0,sK2),sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_44
    | ~ spl13_144
    | ~ spl13_1916
    | ~ spl13_3322 ),
    inference(subsumption_resolution,[],[f43087,f16196])).

fof(f43087,plain,
    ( r1_orders_2(sK1,k1_yellow_0(sK0,sK2),sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_44
    | ~ spl13_144
    | ~ spl13_3322 ),
    inference(subsumption_resolution,[],[f43084,f345])).

fof(f43084,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_144
    | ~ spl13_3322 ),
    inference(resolution,[],[f43081,f952])).

fof(f952,plain,
    ( ! [X2,X1] :
        ( ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_orders_2(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl13_144 ),
    inference(avatar_component_clause,[],[f951])).

fof(f43081,plain,
    ( r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_3322 ),
    inference(avatar_component_clause,[],[f43080])).

fof(f33066,plain,
    ( spl13_1878
    | spl13_33
    | ~ spl13_1852
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2118 ),
    inference(avatar_split_clause,[],[f32553,f17762,f16195,f15788,f15335,f291,f15794])).

fof(f17762,plain,
    ( spl13_2118
  <=> ! [X4] :
        ( ~ m1_subset_1(sK4(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X4,k1_yellow_0(sK0,sK2)))
        | m1_subset_1(sK3(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r1_yellow_0(sK1,X4)
        | ~ r2_lattice3(sK1,X4,k1_yellow_0(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2118])])).

fof(f32553,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_33
    | ~ spl13_1852
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2118 ),
    inference(subsumption_resolution,[],[f32552,f15336])).

fof(f32552,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_33
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2118 ),
    inference(subsumption_resolution,[],[f32547,f292])).

fof(f32547,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2118 ),
    inference(subsumption_resolution,[],[f32545,f16196])).

fof(f32545,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_1876
    | ~ spl13_2118 ),
    inference(resolution,[],[f17763,f15789])).

fof(f17763,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK0,sK2,sK4(sK1,X4,k1_yellow_0(sK0,sK2)))
        | ~ m1_subset_1(sK4(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | m1_subset_1(sK3(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r1_yellow_0(sK1,X4)
        | ~ r2_lattice3(sK1,X4,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_2118 ),
    inference(avatar_component_clause,[],[f17762])).

fof(f32795,plain,
    ( spl13_2178
    | spl13_33
    | ~ spl13_1852
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2116 ),
    inference(avatar_split_clause,[],[f32541,f17750,f16195,f15788,f15335,f291,f18018])).

fof(f17750,plain,
    ( spl13_2116
  <=> ! [X3] :
        ( ~ m1_subset_1(sK4(sK1,X3,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X3,k1_yellow_0(sK0,sK2)))
        | r2_lattice3(sK1,X3,sK3(sK1,X3,k1_yellow_0(sK0,sK2)))
        | r1_yellow_0(sK1,X3)
        | ~ r2_lattice3(sK1,X3,k1_yellow_0(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2116])])).

fof(f32541,plain,
    ( r2_lattice3(sK1,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_33
    | ~ spl13_1852
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2116 ),
    inference(subsumption_resolution,[],[f32540,f15336])).

fof(f32540,plain,
    ( r2_lattice3(sK1,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_33
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2116 ),
    inference(subsumption_resolution,[],[f32539,f292])).

fof(f32539,plain,
    ( r2_lattice3(sK1,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_1876
    | ~ spl13_1916
    | ~ spl13_2116 ),
    inference(subsumption_resolution,[],[f32538,f16196])).

fof(f32538,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | r2_lattice3(sK1,sK2,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_1876
    | ~ spl13_2116 ),
    inference(resolution,[],[f17751,f15789])).

fof(f17751,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,sK2,sK4(sK1,X3,k1_yellow_0(sK0,sK2)))
        | ~ m1_subset_1(sK4(sK1,X3,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r2_lattice3(sK1,X3,sK3(sK1,X3,k1_yellow_0(sK0,sK2)))
        | r1_yellow_0(sK1,X3)
        | ~ r2_lattice3(sK1,X3,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_2116 ),
    inference(avatar_component_clause,[],[f17750])).

fof(f19452,plain,
    ( ~ spl13_26
    | spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | spl13_1917
    | spl13_2179 ),
    inference(avatar_contradiction_clause,[],[f19451])).

fof(f19451,plain,
    ( $false
    | ~ spl13_26
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1917
    | ~ spl13_2179 ),
    inference(subsumption_resolution,[],[f19450,f266])).

fof(f19450,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1917
    | ~ spl13_2179 ),
    inference(subsumption_resolution,[],[f19449,f345])).

fof(f19449,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_1852
    | ~ spl13_1917
    | ~ spl13_2179 ),
    inference(subsumption_resolution,[],[f19448,f15336])).

fof(f19448,plain,
    ( ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_1917
    | ~ spl13_2179 ),
    inference(subsumption_resolution,[],[f19447,f16199])).

fof(f16199,plain,
    ( ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_1917 ),
    inference(avatar_component_clause,[],[f16198])).

fof(f16198,plain,
    ( spl13_1917
  <=> ~ m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1917])])).

fof(f19447,plain,
    ( m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_2179 ),
    inference(subsumption_resolution,[],[f19440,f292])).

fof(f19440,plain,
    ( r1_yellow_0(sK1,sK2)
    | m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_2179 ),
    inference(resolution,[],[f18016,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f18831,plain,
    ( spl13_2172
    | ~ spl13_26
    | ~ spl13_44
    | ~ spl13_286 ),
    inference(avatar_split_clause,[],[f12282,f1782,f344,f265,f17996])).

fof(f1782,plain,
    ( spl13_286
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0)
        | ~ r2_lattice3(sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_286])])).

fof(f12282,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK4(sK1,X1,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X1,k1_yellow_0(sK0,sK2)))
        | r1_orders_2(sK1,sK3(sK1,X1,k1_yellow_0(sK0,sK2)),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_yellow_0(sK1,X1)
        | ~ r2_lattice3(sK1,X1,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_26
    | ~ spl13_44
    | ~ spl13_286 ),
    inference(subsumption_resolution,[],[f12281,f266])).

fof(f12281,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK4(sK1,X1,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X1,k1_yellow_0(sK0,sK2)))
        | r1_orders_2(sK1,sK3(sK1,X1,k1_yellow_0(sK0,sK2)),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_yellow_0(sK1,X1)
        | ~ r2_lattice3(sK1,X1,k1_yellow_0(sK0,sK2))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_44
    | ~ spl13_286 ),
    inference(subsumption_resolution,[],[f12269,f345])).

fof(f12269,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK4(sK1,X1,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X1,k1_yellow_0(sK0,sK2)))
        | r1_orders_2(sK1,sK3(sK1,X1,k1_yellow_0(sK0,sK2)),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_yellow_0(sK1,X1)
        | ~ r2_lattice3(sK1,X1,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_286 ),
    inference(resolution,[],[f1783,f122])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | r1_orders_2(X0,sK3(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1783,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,X0) )
    | ~ spl13_286 ),
    inference(avatar_component_clause,[],[f1782])).

fof(f17786,plain,
    ( spl13_2118
    | ~ spl13_26
    | ~ spl13_44
    | ~ spl13_286 ),
    inference(avatar_split_clause,[],[f12286,f1782,f344,f265,f17762])).

fof(f12286,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK4(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X4,k1_yellow_0(sK0,sK2)))
        | m1_subset_1(sK3(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r1_yellow_0(sK1,X4)
        | ~ r2_lattice3(sK1,X4,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_26
    | ~ spl13_44
    | ~ spl13_286 ),
    inference(subsumption_resolution,[],[f12285,f266])).

fof(f12285,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK4(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X4,k1_yellow_0(sK0,sK2)))
        | m1_subset_1(sK3(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r1_yellow_0(sK1,X4)
        | ~ r2_lattice3(sK1,X4,k1_yellow_0(sK0,sK2))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_44
    | ~ spl13_286 ),
    inference(subsumption_resolution,[],[f12271,f345])).

fof(f12271,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK4(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X4,k1_yellow_0(sK0,sK2)))
        | m1_subset_1(sK3(sK1,X4,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | r1_yellow_0(sK1,X4)
        | ~ r2_lattice3(sK1,X4,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_286 ),
    inference(resolution,[],[f1783,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f17785,plain,
    ( spl13_2116
    | ~ spl13_26
    | ~ spl13_44
    | ~ spl13_286 ),
    inference(avatar_split_clause,[],[f12284,f1782,f344,f265,f17750])).

fof(f12284,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4(sK1,X3,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X3,k1_yellow_0(sK0,sK2)))
        | r2_lattice3(sK1,X3,sK3(sK1,X3,k1_yellow_0(sK0,sK2)))
        | r1_yellow_0(sK1,X3)
        | ~ r2_lattice3(sK1,X3,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_26
    | ~ spl13_44
    | ~ spl13_286 ),
    inference(subsumption_resolution,[],[f12283,f266])).

fof(f12283,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4(sK1,X3,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X3,k1_yellow_0(sK0,sK2)))
        | r2_lattice3(sK1,X3,sK3(sK1,X3,k1_yellow_0(sK0,sK2)))
        | r1_yellow_0(sK1,X3)
        | ~ r2_lattice3(sK1,X3,k1_yellow_0(sK0,sK2))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_44
    | ~ spl13_286 ),
    inference(subsumption_resolution,[],[f12270,f345])).

fof(f12270,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4(sK1,X3,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,sK4(sK1,X3,k1_yellow_0(sK0,sK2)))
        | r2_lattice3(sK1,X3,sK3(sK1,X3,k1_yellow_0(sK0,sK2)))
        | r1_yellow_0(sK1,X3)
        | ~ r2_lattice3(sK1,X3,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_286 ),
    inference(resolution,[],[f1783,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f16989,plain,
    ( spl13_2012
    | ~ spl13_304
    | ~ spl13_1926
    | ~ spl13_1968 ),
    inference(avatar_split_clause,[],[f16606,f16594,f16279,f1949,f16987])).

fof(f1949,plain,
    ( spl13_304
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,X1,k1_yellow_0(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_304])])).

fof(f16594,plain,
    ( spl13_1968
  <=> r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1968])])).

fof(f16606,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_304
    | ~ spl13_1926
    | ~ spl13_1968 ),
    inference(subsumption_resolution,[],[f16602,f16280])).

fof(f16602,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_304
    | ~ spl13_1968 ),
    inference(resolution,[],[f16595,f1950])).

fof(f1950,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_304 ),
    inference(avatar_component_clause,[],[f1949])).

fof(f16595,plain,
    ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),k1_yellow_0(sK0,sK2))
    | ~ spl13_1968 ),
    inference(avatar_component_clause,[],[f16594])).

fof(f16596,plain,
    ( spl13_1968
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1964 ),
    inference(avatar_split_clause,[],[f16582,f16564,f15335,f344,f16594])).

fof(f16582,plain,
    ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),k1_yellow_0(sK0,sK2))
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1964 ),
    inference(subsumption_resolution,[],[f16571,f345])).

fof(f16571,plain,
    ( r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_1852
    | ~ spl13_1964 ),
    inference(resolution,[],[f16565,f15336])).

fof(f16565,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK1,sK2,X1)
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl13_1964 ),
    inference(avatar_component_clause,[],[f16564])).

fof(f16566,plain,
    ( spl13_1964
    | spl13_33
    | ~ spl13_44
    | ~ spl13_220
    | ~ spl13_1852
    | ~ spl13_1878
    | spl13_1917 ),
    inference(avatar_split_clause,[],[f16256,f16198,f15794,f15335,f1219,f344,f291,f16564])).

fof(f1219,plain,
    ( spl13_220
  <=> ! [X5,X4,X6] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3(sK1,X5,X6),u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,X5,X6),X4)
        | r1_yellow_0(sK1,X5)
        | ~ r2_lattice3(sK1,X5,X4)
        | m1_subset_1(sK4(sK1,X5,X6),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_220])])).

fof(f16256,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X1)
        | ~ r2_lattice3(sK1,sK2,X1) )
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_220
    | ~ spl13_1852
    | ~ spl13_1878
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16255,f345])).

fof(f16255,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X1)
        | ~ r2_lattice3(sK1,sK2,X1)
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1)) )
    | ~ spl13_33
    | ~ spl13_220
    | ~ spl13_1852
    | ~ spl13_1878
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16254,f15336])).

fof(f16254,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X1)
        | ~ r2_lattice3(sK1,sK2,X1)
        | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1)) )
    | ~ spl13_33
    | ~ spl13_220
    | ~ spl13_1878
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16253,f16199])).

fof(f16253,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X1)
        | ~ r2_lattice3(sK1,sK2,X1)
        | m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1)) )
    | ~ spl13_33
    | ~ spl13_220
    | ~ spl13_1878 ),
    inference(subsumption_resolution,[],[f16243,f292])).

fof(f16243,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X1)
        | r1_yellow_0(sK1,sK2)
        | ~ r2_lattice3(sK1,sK2,X1)
        | m1_subset_1(sK4(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1)) )
    | ~ spl13_220
    | ~ spl13_1878 ),
    inference(resolution,[],[f15795,f1220])).

fof(f1220,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(sK3(sK1,X5,X6),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,X5,X6),X4)
        | r1_yellow_0(sK1,X5)
        | ~ r2_lattice3(sK1,X5,X4)
        | m1_subset_1(sK4(sK1,X5,X6),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK1)) )
    | ~ spl13_220 ),
    inference(avatar_component_clause,[],[f1219])).

fof(f16485,plain,
    ( spl13_1954
    | spl13_1956
    | ~ spl13_16
    | spl13_33
    | ~ spl13_44
    | ~ spl13_324
    | ~ spl13_400 ),
    inference(avatar_split_clause,[],[f16474,f2485,f2040,f344,f291,f224,f16483,f16477])).

fof(f2485,plain,
    ( spl13_400
  <=> ! [X11,X12] :
        ( ~ m1_subset_1(sK5(sK0,X11),u1_struct_0(sK1))
        | r1_orders_2(sK1,sK3(sK1,X11,sK5(sK0,X11)),X12)
        | ~ r2_lattice3(sK1,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK1))
        | r2_lattice3(sK1,X11,sK4(sK1,X11,sK5(sK0,X11)))
        | r1_yellow_0(sK1,X11)
        | ~ r1_yellow_0(sK0,X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_400])])).

fof(f16474,plain,
    ( ! [X0] :
        ( r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
        | r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_16
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_324
    | ~ spl13_400 ),
    inference(subsumption_resolution,[],[f3788,f292])).

fof(f3788,plain,
    ( ! [X0] :
        ( r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
        | r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_yellow_0(sK1,sK2) )
    | ~ spl13_16
    | ~ spl13_44
    | ~ spl13_324
    | ~ spl13_400 ),
    inference(subsumption_resolution,[],[f3787,f345])).

fof(f3787,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
        | r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_yellow_0(sK1,sK2) )
    | ~ spl13_16
    | ~ spl13_324
    | ~ spl13_400 ),
    inference(forward_demodulation,[],[f3786,f2041])).

fof(f3786,plain,
    ( ! [X0] :
        ( r2_lattice3(sK1,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
        | r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_yellow_0(sK1,sK2)
        | ~ m1_subset_1(sK5(sK0,sK2),u1_struct_0(sK1)) )
    | ~ spl13_16
    | ~ spl13_324
    | ~ spl13_400 ),
    inference(forward_demodulation,[],[f3785,f2041])).

fof(f3785,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK5(sK0,sK2)))
        | r1_yellow_0(sK1,sK2)
        | ~ m1_subset_1(sK5(sK0,sK2),u1_struct_0(sK1)) )
    | ~ spl13_16
    | ~ spl13_324
    | ~ spl13_400 ),
    inference(forward_demodulation,[],[f2491,f2041])).

fof(f2491,plain,
    ( ! [X0] :
        ( r1_orders_2(sK1,sK3(sK1,sK2,sK5(sK0,sK2)),X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,sK4(sK1,sK2,sK5(sK0,sK2)))
        | r1_yellow_0(sK1,sK2)
        | ~ m1_subset_1(sK5(sK0,sK2),u1_struct_0(sK1)) )
    | ~ spl13_16
    | ~ spl13_400 ),
    inference(resolution,[],[f2486,f225])).

fof(f2486,plain,
    ( ! [X12,X11] :
        ( ~ r1_yellow_0(sK0,X11)
        | r1_orders_2(sK1,sK3(sK1,X11,sK5(sK0,X11)),X12)
        | ~ r2_lattice3(sK1,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK1))
        | r2_lattice3(sK1,X11,sK4(sK1,X11,sK5(sK0,X11)))
        | r1_yellow_0(sK1,X11)
        | ~ m1_subset_1(sK5(sK0,X11),u1_struct_0(sK1)) )
    | ~ spl13_400 ),
    inference(avatar_component_clause,[],[f2485])).

fof(f16401,plain,
    ( ~ spl13_1935
    | ~ spl13_26
    | spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | spl13_1917 ),
    inference(avatar_split_clause,[],[f16212,f16198,f15335,f344,f291,f265,f16399])).

fof(f16399,plain,
    ( spl13_1935
  <=> k1_yellow_0(sK0,sK2) != sK3(sK1,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1935])])).

fof(f16212,plain,
    ( k1_yellow_0(sK0,sK2) != sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_26
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16211,f266])).

fof(f16211,plain,
    ( k1_yellow_0(sK0,sK2) != sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16210,f345])).

fof(f16210,plain,
    ( k1_yellow_0(sK0,sK2) != sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_1852
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16209,f15336])).

fof(f16209,plain,
    ( k1_yellow_0(sK0,sK2) != sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16203,f292])).

fof(f16203,plain,
    ( k1_yellow_0(sK0,sK2) != sK3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_1917 ),
    inference(resolution,[],[f16199,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | sK3(X0,X1,X2) != X2
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f16240,plain,
    ( spl13_1878
    | ~ spl13_26
    | spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | spl13_1917 ),
    inference(avatar_split_clause,[],[f16208,f16198,f15335,f344,f291,f265,f15794])).

fof(f16208,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_26
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16207,f266])).

fof(f16207,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16206,f345])).

fof(f16206,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_1852
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16205,f15336])).

fof(f16205,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_33
    | ~ spl13_1917 ),
    inference(subsumption_resolution,[],[f16202,f292])).

fof(f16202,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | r1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_1917 ),
    inference(resolution,[],[f16199,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f15796,plain,
    ( spl13_1876
    | spl13_1878
    | ~ spl13_44
    | ~ spl13_540
    | ~ spl13_1852 ),
    inference(avatar_split_clause,[],[f15779,f15335,f3112,f344,f15794,f15788])).

fof(f3112,plain,
    ( spl13_540
  <=> ! [X0] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X0))
        | m1_subset_1(sK3(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_540])])).

fof(f15779,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | r2_lattice3(sK0,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_44
    | ~ spl13_540
    | ~ spl13_1852 ),
    inference(subsumption_resolution,[],[f15769,f345])).

fof(f15769,plain,
    ( m1_subset_1(sK3(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | r2_lattice3(sK0,sK2,sK4(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_540
    | ~ spl13_1852 ),
    inference(resolution,[],[f3113,f15336])).

fof(f3113,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK1,sK2,X0)
        | m1_subset_1(sK3(sK1,sK2,X0),u1_struct_0(sK1))
        | r2_lattice3(sK0,sK2,sK4(sK1,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_540 ),
    inference(avatar_component_clause,[],[f3112])).

fof(f15653,plain,
    ( spl13_1854
    | spl13_35
    | ~ spl13_44
    | ~ spl13_1806
    | ~ spl13_1852 ),
    inference(avatar_split_clause,[],[f15413,f15335,f15094,f344,f297,f15341])).

fof(f15341,plain,
    ( spl13_1854
  <=> r2_lattice3(sK0,sK2,sK7(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1854])])).

fof(f297,plain,
    ( spl13_35
  <=> k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).

fof(f15094,plain,
    ( spl13_1806
  <=> ! [X0] :
        ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,X0))
        | k1_yellow_0(sK1,sK2) = X0
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1806])])).

fof(f15413,plain,
    ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_35
    | ~ spl13_44
    | ~ spl13_1806
    | ~ spl13_1852 ),
    inference(subsumption_resolution,[],[f15412,f345])).

fof(f15412,plain,
    ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_35
    | ~ spl13_1806
    | ~ spl13_1852 ),
    inference(subsumption_resolution,[],[f15362,f298])).

fof(f298,plain,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
    | ~ spl13_35 ),
    inference(avatar_component_clause,[],[f297])).

fof(f15362,plain,
    ( k1_yellow_0(sK0,sK2) = k1_yellow_0(sK1,sK2)
    | r2_lattice3(sK0,sK2,sK7(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_1806
    | ~ spl13_1852 ),
    inference(resolution,[],[f15336,f15095])).

fof(f15095,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK1,sK2,X0)
        | k1_yellow_0(sK1,sK2) = X0
        | r2_lattice3(sK0,sK2,sK7(sK1,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_1806 ),
    inference(avatar_component_clause,[],[f15094])).

fof(f15425,plain,
    ( ~ spl13_26
    | ~ spl13_32
    | spl13_35
    | ~ spl13_44
    | ~ spl13_1852
    | spl13_1857 ),
    inference(avatar_contradiction_clause,[],[f15424])).

fof(f15424,plain,
    ( $false
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_35
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1857 ),
    inference(subsumption_resolution,[],[f15423,f266])).

fof(f15423,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl13_32
    | ~ spl13_35
    | ~ spl13_44
    | ~ spl13_1852
    | ~ spl13_1857 ),
    inference(subsumption_resolution,[],[f15422,f345])).

fof(f15422,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_32
    | ~ spl13_35
    | ~ spl13_1852
    | ~ spl13_1857 ),
    inference(subsumption_resolution,[],[f15421,f289])).

fof(f289,plain,
    ( r1_yellow_0(sK1,sK2)
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl13_32
  <=> r1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f15421,plain,
    ( ~ r1_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_35
    | ~ spl13_1852
    | ~ spl13_1857 ),
    inference(subsumption_resolution,[],[f15420,f15336])).

fof(f15420,plain,
    ( ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ r1_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_35
    | ~ spl13_1857 ),
    inference(subsumption_resolution,[],[f15417,f298])).

fof(f15417,plain,
    ( k1_yellow_0(sK0,sK2) = k1_yellow_0(sK1,sK2)
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ r1_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl13_1857 ),
    inference(resolution,[],[f15351,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
                & r2_lattice3(X0,X1,sK7(X0,X1,X2))
                & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f81,f82])).

fof(f82,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
        & r2_lattice3(X0,X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',d9_yellow_0)).

fof(f15351,plain,
    ( ~ m1_subset_1(sK7(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ spl13_1857 ),
    inference(avatar_component_clause,[],[f15350])).

fof(f15350,plain,
    ( spl13_1857
  <=> ~ m1_subset_1(sK7(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1857])])).

fof(f15357,plain,
    ( spl13_1
    | ~ spl13_4
    | spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_44
    | ~ spl13_344
    | spl13_1853 ),
    inference(avatar_contradiction_clause,[],[f15354])).

fof(f15354,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_44
    | ~ spl13_344
    | ~ spl13_1853 ),
    inference(unit_resulting_resolution,[],[f169,f183,f190,f211,f218,f2130,f345,f15339,f411])).

fof(f411,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_yellow_0(X1,X0)
      | r2_lattice3(X1,X2,X4)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f158,f135])).

fof(f158,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_lattice3(X1,X2,X4)
      | ~ r2_lattice3(X0,X2,X3)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ! [X4] :
                  ( ( ( r2_lattice3(X1,X2,X4)
                      | ~ r2_lattice3(X0,X2,X3) )
                    & ( r1_lattice3(X1,X2,X4)
                      | ~ r1_lattice3(X0,X2,X3) ) )
                  | X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X3 = X4
                   => ( ( r2_lattice3(X0,X2,X3)
                       => r2_lattice3(X1,X2,X4) )
                      & ( r1_lattice3(X0,X2,X3)
                       => r1_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t62_yellow_0)).

fof(f15339,plain,
    ( ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_1853 ),
    inference(avatar_component_clause,[],[f15338])).

fof(f15338,plain,
    ( spl13_1853
  <=> ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1853])])).

fof(f2130,plain,
    ( r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_344 ),
    inference(avatar_component_clause,[],[f2129])).

fof(f2129,plain,
    ( spl13_344
  <=> r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_344])])).

fof(f211,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl13_12
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f15352,plain,
    ( ~ spl13_1853
    | ~ spl13_1855
    | ~ spl13_1857
    | spl13_35
    | ~ spl13_44
    | ~ spl13_286
    | ~ spl13_1350 ),
    inference(avatar_split_clause,[],[f12277,f11028,f1782,f344,f297,f15350,f15344,f15338])).

fof(f15344,plain,
    ( spl13_1855
  <=> ~ r2_lattice3(sK0,sK2,sK7(sK1,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1855])])).

fof(f11028,plain,
    ( spl13_1350
  <=> ! [X5] :
        ( ~ r1_orders_2(sK1,X5,sK7(sK1,sK2,X5))
        | ~ r2_lattice3(sK1,sK2,X5)
        | k1_yellow_0(sK1,sK2) = X5
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1350])])).

fof(f12277,plain,
    ( ~ m1_subset_1(sK7(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK0,sK2,sK7(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_35
    | ~ spl13_44
    | ~ spl13_286
    | ~ spl13_1350 ),
    inference(subsumption_resolution,[],[f12276,f345])).

fof(f12276,plain,
    ( ~ m1_subset_1(sK7(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK0,sK2,sK7(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_35
    | ~ spl13_286
    | ~ spl13_1350 ),
    inference(subsumption_resolution,[],[f12265,f298])).

fof(f12265,plain,
    ( ~ m1_subset_1(sK7(sK1,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK1))
    | ~ r2_lattice3(sK0,sK2,sK7(sK1,sK2,k1_yellow_0(sK0,sK2)))
    | ~ r2_lattice3(sK1,sK2,k1_yellow_0(sK0,sK2))
    | k1_yellow_0(sK0,sK2) = k1_yellow_0(sK1,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_286
    | ~ spl13_1350 ),
    inference(resolution,[],[f1783,f11029])).

fof(f11029,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK1,X5,sK7(sK1,sK2,X5))
        | ~ r2_lattice3(sK1,sK2,X5)
        | k1_yellow_0(sK1,sK2) = X5
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    | ~ spl13_1350 ),
    inference(avatar_component_clause,[],[f11028])).

fof(f15096,plain,
    ( spl13_1806
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_1464 ),
    inference(avatar_split_clause,[],[f12485,f12469,f288,f265,f15094])).

fof(f12469,plain,
    ( spl13_1464
  <=> ! [X5] :
        ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,X5))
        | ~ m1_subset_1(sK7(sK1,sK2,X5),u1_struct_0(sK1))
        | k1_yellow_0(sK1,sK2) = X5
        | ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1464])])).

fof(f12485,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,X0))
        | k1_yellow_0(sK1,sK2) = X0
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_1464 ),
    inference(subsumption_resolution,[],[f12484,f266])).

fof(f12484,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,X0))
        | k1_yellow_0(sK1,sK2) = X0
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_32
    | ~ spl13_1464 ),
    inference(subsumption_resolution,[],[f12483,f289])).

fof(f12483,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,X0))
        | k1_yellow_0(sK1,sK2) = X0
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r1_yellow_0(sK1,sK2)
        | ~ l1_orders_2(sK1) )
    | ~ spl13_1464 ),
    inference(duplicate_literal_removal,[],[f12481])).

fof(f12481,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,X0))
        | k1_yellow_0(sK1,sK2) = X0
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | k1_yellow_0(sK1,sK2) = X0
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ r1_yellow_0(sK1,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_1464 ),
    inference(resolution,[],[f12470,f128])).

fof(f12470,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(sK7(sK1,sK2,X5),u1_struct_0(sK1))
        | r2_lattice3(sK0,sK2,sK7(sK1,sK2,X5))
        | k1_yellow_0(sK1,sK2) = X5
        | ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    | ~ spl13_1464 ),
    inference(avatar_component_clause,[],[f12469])).

fof(f12471,plain,
    ( spl13_1464
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_126 ),
    inference(avatar_split_clause,[],[f11103,f845,f288,f265,f12469])).

fof(f11103,plain,
    ( ! [X5] :
        ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,X5))
        | ~ m1_subset_1(sK7(sK1,sK2,X5),u1_struct_0(sK1))
        | k1_yellow_0(sK1,sK2) = X5
        | ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    | ~ spl13_26
    | ~ spl13_32
    | ~ spl13_126 ),
    inference(subsumption_resolution,[],[f11102,f266])).

fof(f11102,plain,
    ( ! [X5] :
        ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,X5))
        | ~ m1_subset_1(sK7(sK1,sK2,X5),u1_struct_0(sK1))
        | k1_yellow_0(sK1,sK2) = X5
        | ~ r2_lattice3(sK1,sK2,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_32
    | ~ spl13_126 ),
    inference(subsumption_resolution,[],[f11094,f289])).

fof(f11094,plain,
    ( ! [X5] :
        ( r2_lattice3(sK0,sK2,sK7(sK1,sK2,X5))
        | ~ m1_subset_1(sK7(sK1,sK2,X5),u1_struct_0(sK1))
        | k1_yellow_0(sK1,sK2) = X5
        | ~ r2_lattice3(sK1,sK2,X5)
        | ~ r1_yellow_0(sK1,sK2)
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_126 ),
    inference(resolution,[],[f846,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f11030,plain,
    ( spl13_1350
    | ~ spl13_26
    | ~ spl13_32 ),
    inference(avatar_split_clause,[],[f10890,f288,f265,f11028])).

fof(f10890,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK1,X5,sK7(sK1,sK2,X5))
        | ~ r2_lattice3(sK1,sK2,X5)
        | k1_yellow_0(sK1,sK2) = X5
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    | ~ spl13_26
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f10882,f266])).

fof(f10882,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK1,X5,sK7(sK1,sK2,X5))
        | ~ r2_lattice3(sK1,sK2,X5)
        | k1_yellow_0(sK1,sK2) = X5
        | ~ m1_subset_1(X5,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_32 ),
    inference(resolution,[],[f289,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f11012,plain,
    ( spl13_86
    | ~ spl13_4
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f10865,f224,f182,f572])).

fof(f572,plain,
    ( spl13_86
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,sK2,X0))
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_86])])).

fof(f10865,plain,
    ( ! [X13] :
        ( ~ r1_orders_2(sK0,X13,sK6(sK0,sK2,X13))
        | ~ r2_lattice3(sK0,sK2,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | sK5(sK0,sK2) = X13 )
    | ~ spl13_4
    | ~ spl13_16 ),
    inference(subsumption_resolution,[],[f10857,f183])).

fof(f10857,plain,
    ( ! [X13] :
        ( ~ r1_orders_2(sK0,X13,sK6(sK0,sK2,X13))
        | ~ r2_lattice3(sK0,sK2,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | sK5(sK0,sK2) = X13
        | ~ l1_orders_2(sK0) )
    | ~ spl13_16 ),
    inference(resolution,[],[f225,f113])).

fof(f113,plain,(
    ! [X0,X7,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | ~ r1_orders_2(X0,X7,sK6(X0,X1,X7))
      | ~ r2_lattice3(X0,X1,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | sK5(X0,X1) = X7
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f3114,plain,
    ( spl13_540
    | ~ spl13_26
    | spl13_33
    | ~ spl13_372 ),
    inference(avatar_split_clause,[],[f2404,f2359,f291,f265,f3112])).

fof(f2359,plain,
    ( spl13_372
  <=> ! [X3] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X3))
        | ~ m1_subset_1(sK4(sK1,sK2,X3),u1_struct_0(sK1))
        | m1_subset_1(sK3(sK1,sK2,X3),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_372])])).

fof(f2404,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X0))
        | m1_subset_1(sK3(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl13_26
    | ~ spl13_33
    | ~ spl13_372 ),
    inference(subsumption_resolution,[],[f2403,f266])).

fof(f2403,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X0))
        | m1_subset_1(sK3(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_33
    | ~ spl13_372 ),
    inference(subsumption_resolution,[],[f2402,f292])).

fof(f2402,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X0))
        | m1_subset_1(sK3(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_yellow_0(sK1,sK2)
        | ~ l1_orders_2(sK1) )
    | ~ spl13_372 ),
    inference(duplicate_literal_removal,[],[f2398])).

fof(f2398,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X0))
        | m1_subset_1(sK3(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(sK3(sK1,sK2,X0),u1_struct_0(sK1))
        | r1_yellow_0(sK1,sK2)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_372 ),
    inference(resolution,[],[f2360,f114])).

fof(f2360,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK4(sK1,sK2,X3),u1_struct_0(sK1))
        | r2_lattice3(sK0,sK2,sK4(sK1,sK2,X3))
        | m1_subset_1(sK3(sK1,sK2,X3),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl13_372 ),
    inference(avatar_component_clause,[],[f2359])).

fof(f2487,plain,
    ( spl13_400
    | ~ spl13_4
    | ~ spl13_186 ),
    inference(avatar_split_clause,[],[f1117,f1101,f182,f2485])).

fof(f1101,plain,
    ( spl13_186
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK1,sK3(sK1,X1,X0),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r2_lattice3(sK1,X1,sK4(sK1,X1,X0))
        | r1_yellow_0(sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_186])])).

fof(f1117,plain,
    ( ! [X12,X11] :
        ( ~ m1_subset_1(sK5(sK0,X11),u1_struct_0(sK1))
        | r1_orders_2(sK1,sK3(sK1,X11,sK5(sK0,X11)),X12)
        | ~ r2_lattice3(sK1,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK1))
        | r2_lattice3(sK1,X11,sK4(sK1,X11,sK5(sK0,X11)))
        | r1_yellow_0(sK1,X11)
        | ~ r1_yellow_0(sK0,X11) )
    | ~ spl13_4
    | ~ spl13_186 ),
    inference(subsumption_resolution,[],[f1110,f183])).

fof(f1110,plain,
    ( ! [X12,X11] :
        ( ~ m1_subset_1(sK5(sK0,X11),u1_struct_0(sK1))
        | r1_orders_2(sK1,sK3(sK1,X11,sK5(sK0,X11)),X12)
        | ~ r2_lattice3(sK1,X11,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK1))
        | r2_lattice3(sK1,X11,sK4(sK1,X11,sK5(sK0,X11)))
        | r1_yellow_0(sK1,X11)
        | ~ r1_yellow_0(sK0,X11)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_186 ),
    inference(resolution,[],[f1102,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1102,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,sK3(sK1,X1,X0),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r2_lattice3(sK1,X1,sK4(sK1,X1,X0))
        | r1_yellow_0(sK1,X1) )
    | ~ spl13_186 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f2373,plain,
    ( spl13_372
    | ~ spl13_26
    | spl13_33
    | ~ spl13_126 ),
    inference(avatar_split_clause,[],[f1402,f845,f291,f265,f2359])).

fof(f1402,plain,
    ( ! [X3] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X3))
        | ~ m1_subset_1(sK4(sK1,sK2,X3),u1_struct_0(sK1))
        | m1_subset_1(sK3(sK1,sK2,X3),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1)) )
    | ~ spl13_26
    | ~ spl13_33
    | ~ spl13_126 ),
    inference(subsumption_resolution,[],[f1401,f266])).

fof(f1401,plain,
    ( ! [X3] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X3))
        | ~ m1_subset_1(sK4(sK1,sK2,X3),u1_struct_0(sK1))
        | m1_subset_1(sK3(sK1,sK2,X3),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_33
    | ~ spl13_126 ),
    inference(subsumption_resolution,[],[f1392,f292])).

fof(f1392,plain,
    ( ! [X3] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X3))
        | ~ m1_subset_1(sK4(sK1,sK2,X3),u1_struct_0(sK1))
        | m1_subset_1(sK3(sK1,sK2,X3),u1_struct_0(sK1))
        | r1_yellow_0(sK1,sK2)
        | ~ r2_lattice3(sK1,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_126 ),
    inference(resolution,[],[f846,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2371,plain,
    ( spl13_370
    | ~ spl13_26
    | spl13_33
    | ~ spl13_126 ),
    inference(avatar_split_clause,[],[f1400,f845,f291,f265,f2353])).

fof(f1400,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X2))
        | ~ m1_subset_1(sK4(sK1,sK2,X2),u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,sK3(sK1,sK2,X2))
        | ~ r2_lattice3(sK1,sK2,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl13_26
    | ~ spl13_33
    | ~ spl13_126 ),
    inference(subsumption_resolution,[],[f1399,f266])).

fof(f1399,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X2))
        | ~ m1_subset_1(sK4(sK1,sK2,X2),u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,sK3(sK1,sK2,X2))
        | ~ r2_lattice3(sK1,sK2,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_33
    | ~ spl13_126 ),
    inference(subsumption_resolution,[],[f1391,f292])).

fof(f1391,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,sK2,sK4(sK1,sK2,X2))
        | ~ m1_subset_1(sK4(sK1,sK2,X2),u1_struct_0(sK1))
        | r2_lattice3(sK1,sK2,sK3(sK1,sK2,X2))
        | r1_yellow_0(sK1,sK2)
        | ~ r2_lattice3(sK1,sK2,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_126 ),
    inference(resolution,[],[f846,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2257,plain,
    ( spl13_346
    | ~ spl13_86
    | ~ spl13_324 ),
    inference(avatar_split_clause,[],[f2229,f2040,f572,f2255])).

fof(f2229,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,sK2) = X0
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK2,X0))
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_86
    | ~ spl13_324 ),
    inference(backward_demodulation,[],[f2041,f573])).

fof(f573,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,sK2,X0))
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,sK2) = X0 )
    | ~ spl13_86 ),
    inference(avatar_component_clause,[],[f572])).

fof(f2196,plain,
    ( spl13_324
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_74
    | spl13_323
    | ~ spl13_344 ),
    inference(avatar_split_clause,[],[f2182,f2129,f2034,f529,f224,f182,f2040])).

fof(f529,plain,
    ( spl13_74
  <=> m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f2034,plain,
    ( spl13_323
  <=> ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,k1_yellow_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_323])])).

fof(f2182,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_74
    | ~ spl13_323
    | ~ spl13_344 ),
    inference(subsumption_resolution,[],[f2181,f183])).

fof(f2181,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_16
    | ~ spl13_74
    | ~ spl13_323
    | ~ spl13_344 ),
    inference(subsumption_resolution,[],[f2180,f225])).

fof(f2180,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_74
    | ~ spl13_323
    | ~ spl13_344 ),
    inference(subsumption_resolution,[],[f2179,f530])).

fof(f530,plain,
    ( m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_74 ),
    inference(avatar_component_clause,[],[f529])).

fof(f2179,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_323
    | ~ spl13_344 ),
    inference(subsumption_resolution,[],[f2178,f2130])).

fof(f2178,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_323 ),
    inference(resolution,[],[f2035,f112])).

fof(f2035,plain,
    ( ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,k1_yellow_0(sK0,sK2)))
    | ~ spl13_323 ),
    inference(avatar_component_clause,[],[f2034])).

fof(f2140,plain,
    ( ~ spl13_4
    | ~ spl13_16
    | spl13_345 ),
    inference(avatar_contradiction_clause,[],[f2139])).

fof(f2139,plain,
    ( $false
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_345 ),
    inference(subsumption_resolution,[],[f2138,f183])).

fof(f2138,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl13_16
    | ~ spl13_345 ),
    inference(subsumption_resolution,[],[f2136,f225])).

fof(f2136,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_345 ),
    inference(resolution,[],[f2133,f322])).

fof(f322,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f157,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',dt_k1_yellow_0)).

fof(f157,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f2133,plain,
    ( ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_345 ),
    inference(avatar_component_clause,[],[f2132])).

fof(f2132,plain,
    ( spl13_345
  <=> ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_345])])).

fof(f2134,plain,
    ( ~ spl13_345
    | spl13_324
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_74
    | spl13_321 ),
    inference(avatar_split_clause,[],[f2047,f2028,f529,f224,f182,f2040,f2132])).

fof(f2028,plain,
    ( spl13_321
  <=> ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_321])])).

fof(f2047,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_74
    | ~ spl13_321 ),
    inference(subsumption_resolution,[],[f2046,f183])).

fof(f2046,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ l1_orders_2(sK0)
    | ~ spl13_16
    | ~ spl13_74
    | ~ spl13_321 ),
    inference(subsumption_resolution,[],[f2045,f225])).

fof(f2045,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_74
    | ~ spl13_321 ),
    inference(subsumption_resolution,[],[f2043,f530])).

fof(f2043,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK2))
    | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_321 ),
    inference(resolution,[],[f2029,f111])).

fof(f2029,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_321 ),
    inference(avatar_component_clause,[],[f2028])).

fof(f2042,plain,
    ( ~ spl13_321
    | ~ spl13_323
    | spl13_324
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_74
    | ~ spl13_210 ),
    inference(avatar_split_clause,[],[f1241,f1197,f529,f224,f182,f2040,f2034,f2028])).

fof(f1197,plain,
    ( spl13_210
  <=> ! [X1] :
        ( ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,X1))
        | ~ m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X1) = sK5(sK0,sK2)
        | ~ r2_lattice3(sK0,X1,sK6(sK0,sK2,k1_yellow_0(sK0,X1)))
        | ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,X1)),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_210])])).

fof(f1241,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_74
    | ~ spl13_210 ),
    inference(subsumption_resolution,[],[f1240,f183])).

fof(f1240,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl13_16
    | ~ spl13_74
    | ~ spl13_210 ),
    inference(subsumption_resolution,[],[f1239,f225])).

fof(f1239,plain,
    ( k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_74
    | ~ spl13_210 ),
    inference(subsumption_resolution,[],[f1238,f530])).

fof(f1238,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_210 ),
    inference(duplicate_literal_removal,[],[f1237])).

fof(f1237,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | k1_yellow_0(sK0,sK2) = sK5(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK6(sK0,sK2,k1_yellow_0(sK0,sK2)))
    | ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl13_210 ),
    inference(resolution,[],[f1198,f322])).

fof(f1198,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,X1))
        | ~ m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X1) = sK5(sK0,sK2)
        | ~ r2_lattice3(sK0,X1,sK6(sK0,sK2,k1_yellow_0(sK0,X1)))
        | ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,X1)),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X1) )
    | ~ spl13_210 ),
    inference(avatar_component_clause,[],[f1197])).

fof(f1951,plain,
    ( spl13_304
    | ~ spl13_16
    | ~ spl13_74
    | ~ spl13_180 ),
    inference(avatar_split_clause,[],[f1095,f1082,f529,f224,f1949])).

fof(f1082,plain,
    ( spl13_180
  <=> ! [X3,X5,X4] :
        ( ~ r1_orders_2(sK0,X3,k1_yellow_0(sK0,X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,X5)
        | ~ r2_lattice3(sK0,X4,X5)
        | ~ r1_yellow_0(sK0,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_180])])).

fof(f1095,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,X1,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_16
    | ~ spl13_74
    | ~ spl13_180 ),
    inference(subsumption_resolution,[],[f1094,f530])).

fof(f1094,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,X1,k1_yellow_0(sK0,sK2)) )
    | ~ spl13_16
    | ~ spl13_180 ),
    inference(resolution,[],[f1083,f225])).

fof(f1083,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_yellow_0(sK0,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,X5)
        | ~ r2_lattice3(sK0,X4,X5)
        | ~ r1_orders_2(sK0,X3,k1_yellow_0(sK0,X4)) )
    | ~ spl13_180 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1861,plain,
    ( spl13_288
    | ~ spl13_44
    | ~ spl13_98
    | ~ spl13_286 ),
    inference(avatar_split_clause,[],[f1831,f1782,f618,f344,f1859])).

fof(f1831,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,X0)
        | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0) )
    | ~ spl13_44
    | ~ spl13_98
    | ~ spl13_286 ),
    inference(subsumption_resolution,[],[f1830,f345])).

fof(f1830,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
        | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0) )
    | ~ spl13_98
    | ~ spl13_286 ),
    inference(duplicate_literal_removal,[],[f1826])).

fof(f1826,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
        | r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0) )
    | ~ spl13_98
    | ~ spl13_286 ),
    inference(resolution,[],[f1783,f619])).

fof(f1805,plain,
    ( spl13_286
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_72
    | ~ spl13_134 ),
    inference(avatar_split_clause,[],[f1412,f895,f507,f224,f182,f1782])).

fof(f895,plain,
    ( spl13_134
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_134])])).

fof(f1412,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0)
        | ~ r2_lattice3(sK0,sK2,X0) )
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_72
    | ~ spl13_134 ),
    inference(subsumption_resolution,[],[f1411,f508])).

fof(f1411,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_4
    | ~ spl13_16
    | ~ spl13_134 ),
    inference(subsumption_resolution,[],[f1410,f183])).

fof(f1410,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl13_16
    | ~ spl13_134 ),
    inference(subsumption_resolution,[],[f1409,f225])).

fof(f1409,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0)
        | ~ r2_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,sK2)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_134 ),
    inference(resolution,[],[f896,f354])).

fof(f354,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f156,f140])).

fof(f156,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f896,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0) )
    | ~ spl13_134 ),
    inference(avatar_component_clause,[],[f895])).

fof(f1221,plain,
    ( spl13_220
    | ~ spl13_26
    | ~ spl13_98 ),
    inference(avatar_split_clause,[],[f636,f618,f265,f1219])).

fof(f636,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3(sK1,X5,X6),u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,X5,X6),X4)
        | r1_yellow_0(sK1,X5)
        | ~ r2_lattice3(sK1,X5,X4)
        | m1_subset_1(sK4(sK1,X5,X6),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK1)) )
    | ~ spl13_26
    | ~ spl13_98 ),
    inference(subsumption_resolution,[],[f631,f266])).

fof(f631,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3(sK1,X5,X6),u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,X5,X6),X4)
        | r1_yellow_0(sK1,X5)
        | ~ r2_lattice3(sK1,X5,X4)
        | m1_subset_1(sK4(sK1,X5,X6),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_98 ),
    inference(duplicate_literal_removal,[],[f630])).

fof(f630,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK3(sK1,X5,X6),u1_struct_0(sK1))
        | r1_orders_2(sK0,sK3(sK1,X5,X6),X4)
        | r1_yellow_0(sK1,X5)
        | ~ r2_lattice3(sK1,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1))
        | m1_subset_1(sK4(sK1,X5,X6),u1_struct_0(sK1))
        | ~ r2_lattice3(sK1,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_98 ),
    inference(resolution,[],[f619,f120])).

fof(f120,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,sK3(X0,X1,X2),X4)
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1199,plain,
    ( spl13_210
    | ~ spl13_4
    | ~ spl13_86 ),
    inference(avatar_split_clause,[],[f589,f572,f182,f1197])).

fof(f589,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,X1))
        | ~ m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X1) = sK5(sK0,sK2)
        | ~ r2_lattice3(sK0,X1,sK6(sK0,sK2,k1_yellow_0(sK0,X1)))
        | ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,X1)),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X1) )
    | ~ spl13_4
    | ~ spl13_86 ),
    inference(subsumption_resolution,[],[f586,f183])).

fof(f586,plain,
    ( ! [X1] :
        ( ~ r2_lattice3(sK0,sK2,k1_yellow_0(sK0,X1))
        | ~ m1_subset_1(k1_yellow_0(sK0,X1),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X1) = sK5(sK0,sK2)
        | ~ r2_lattice3(sK0,X1,sK6(sK0,sK2,k1_yellow_0(sK0,X1)))
        | ~ m1_subset_1(sK6(sK0,sK2,k1_yellow_0(sK0,X1)),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_86 ),
    inference(resolution,[],[f573,f354])).

fof(f1103,plain,
    ( spl13_186
    | ~ spl13_26
    | ~ spl13_80 ),
    inference(avatar_split_clause,[],[f552,f547,f265,f1101])).

fof(f547,plain,
    ( spl13_80
  <=> ! [X1,X0] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f552,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK1,sK3(sK1,X1,X0),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r2_lattice3(sK1,X1,sK4(sK1,X1,X0))
        | r1_yellow_0(sK1,X1) )
    | ~ spl13_26
    | ~ spl13_80 ),
    inference(subsumption_resolution,[],[f551,f266])).

fof(f551,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK1,sK3(sK1,X1,X0),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r2_lattice3(sK1,X1,sK4(sK1,X1,X0))
        | r1_yellow_0(sK1,X1)
        | ~ l1_orders_2(sK1) )
    | ~ spl13_80 ),
    inference(duplicate_literal_removal,[],[f550])).

fof(f550,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,X1,X0)
        | r1_orders_2(sK1,sK3(sK1,X1,X0),X2)
        | ~ r2_lattice3(sK1,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r2_lattice3(sK1,X1,sK4(sK1,X1,X0))
        | r1_yellow_0(sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1) )
    | ~ spl13_80 ),
    inference(resolution,[],[f548,f121])).

fof(f121,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | r1_orders_2(X0,sK3(X0,X1,X2),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f548,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_lattice3(sK0,X0,X1) )
    | ~ spl13_80 ),
    inference(avatar_component_clause,[],[f547])).

fof(f1084,plain,
    ( spl13_180
    | ~ spl13_4
    | ~ spl13_94 ),
    inference(avatar_split_clause,[],[f667,f606,f182,f1082])).

fof(f606,plain,
    ( spl13_94
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f667,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_orders_2(sK0,X3,k1_yellow_0(sK0,X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,X5)
        | ~ r2_lattice3(sK0,X4,X5)
        | ~ r1_yellow_0(sK0,X4) )
    | ~ spl13_4
    | ~ spl13_94 ),
    inference(subsumption_resolution,[],[f664,f183])).

fof(f664,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_orders_2(sK0,X3,k1_yellow_0(sK0,X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,X5)
        | ~ r2_lattice3(sK0,X4,X5)
        | ~ r1_yellow_0(sK0,X4)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_94 ),
    inference(duplicate_literal_removal,[],[f661])).

fof(f661,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_orders_2(sK0,X3,k1_yellow_0(sK0,X4))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_orders_2(sK0,X3,X5)
        | ~ r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X4)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_94 ),
    inference(resolution,[],[f607,f354])).

fof(f607,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl13_94 ),
    inference(avatar_component_clause,[],[f606])).

fof(f960,plain,
    ( ~ spl13_20
    | ~ spl13_142 ),
    inference(avatar_contradiction_clause,[],[f954])).

fof(f954,plain,
    ( $false
    | ~ spl13_20
    | ~ spl13_142 ),
    inference(unit_resulting_resolution,[],[f239,f949,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t7_boole)).

fof(f949,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl13_142 ),
    inference(avatar_component_clause,[],[f948])).

fof(f948,plain,
    ( spl13_142
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_142])])).

fof(f239,plain,
    ( r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl13_20
  <=> r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f953,plain,
    ( spl13_142
    | spl13_144
    | ~ spl13_72
    | ~ spl13_104 ),
    inference(avatar_split_clause,[],[f652,f644,f507,f951,f948])).

fof(f644,plain,
    ( spl13_104
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_104])])).

fof(f652,plain,
    ( ! [X2,X1] :
        ( ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | r1_orders_2(sK1,X1,X2)
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl13_72
    | ~ spl13_104 ),
    inference(subsumption_resolution,[],[f650,f508])).

fof(f650,plain,
    ( ! [X2,X1] :
        ( ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X2)
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl13_104 ),
    inference(resolution,[],[f645,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t2_subset)).

fof(f645,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl13_104 ),
    inference(avatar_component_clause,[],[f644])).

fof(f897,plain,
    ( spl13_134
    | ~ spl13_20
    | ~ spl13_74
    | ~ spl13_104 ),
    inference(avatar_split_clause,[],[f651,f644,f529,f238,f895])).

fof(f651,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0) )
    | ~ spl13_20
    | ~ spl13_74
    | ~ spl13_104 ),
    inference(subsumption_resolution,[],[f649,f530])).

fof(f649,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
        | r1_orders_2(sK1,k1_yellow_0(sK0,sK2),X0) )
    | ~ spl13_20
    | ~ spl13_104 ),
    inference(resolution,[],[f645,f239])).

fof(f847,plain,
    ( spl13_126
    | spl13_1
    | ~ spl13_4
    | ~ spl13_14
    | ~ spl13_82 ),
    inference(avatar_split_clause,[],[f570,f561,f217,f182,f168,f845])).

fof(f561,plain,
    ( spl13_82
  <=> ! [X1,X0] :
        ( ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(X1,sK2,X0)
        | ~ m1_yellow_0(sK1,X1)
        | ~ l1_orders_2(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_82])])).

fof(f570,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(sK0,sK2,X0)
        | ~ r2_lattice3(sK1,sK2,X0) )
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_14
    | ~ spl13_82 ),
    inference(subsumption_resolution,[],[f569,f169])).

fof(f569,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(sK0,sK2,X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | v2_struct_0(sK0) )
    | ~ spl13_4
    | ~ spl13_14
    | ~ spl13_82 ),
    inference(subsumption_resolution,[],[f568,f183])).

fof(f568,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(sK0,sK2,X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_14
    | ~ spl13_82 ),
    inference(resolution,[],[f562,f218])).

fof(f562,plain,
    ( ! [X0,X1] :
        ( ~ m1_yellow_0(sK1,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(X1,sK2,X0)
        | ~ r2_lattice3(sK1,sK2,X0)
        | ~ l1_orders_2(X1)
        | v2_struct_0(X1) )
    | ~ spl13_82 ),
    inference(avatar_component_clause,[],[f561])).

fof(f646,plain,
    ( spl13_104
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f638,f507,f217,f210,f182,f644])).

fof(f638,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_14
    | ~ spl13_72 ),
    inference(subsumption_resolution,[],[f505,f508])).

fof(f505,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,X1) )
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f504,f183])).

fof(f504,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_12
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f503,f218])).

fof(f503,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_yellow_0(sK1,sK0)
        | r1_orders_2(sK1,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_12 ),
    inference(resolution,[],[f501,f211])).

fof(f501,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v4_yellow_0(X1,X0)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f155,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t1_subset)).

fof(f155,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f154])).

fof(f154,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X1,X4,X5)
                          | ~ r2_hidden(X4,u1_struct_0(X1))
                          | ~ r1_orders_2(X0,X2,X3)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t61_yellow_0)).

fof(f620,plain,
    ( spl13_98
    | ~ spl13_4
    | ~ spl13_14
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f614,f507,f217,f182,f618])).

fof(f614,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl13_4
    | ~ spl13_14
    | ~ spl13_72 ),
    inference(subsumption_resolution,[],[f613,f508])).

fof(f613,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl13_4
    | ~ spl13_14
    | ~ spl13_72 ),
    inference(subsumption_resolution,[],[f434,f508])).

fof(f434,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1) )
    | ~ spl13_4
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f431,f183])).

fof(f431,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl13_14 ),
    inference(resolution,[],[f153,f218])).

fof(f153,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X5)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X1,X4,X5)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t60_yellow_0)).

fof(f608,plain,
    ( spl13_94
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f406,f182,f175,f606])).

fof(f175,plain,
    ( spl13_2
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f406,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl13_2
    | ~ spl13_4 ),
    inference(subsumption_resolution,[],[f405,f183])).

fof(f405,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,X2,X1) )
    | ~ spl13_2 ),
    inference(resolution,[],[f138,f176])).

fof(f176,plain,
    ( v4_orders_2(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f175])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t26_orders_2)).

fof(f563,plain,
    ( spl13_82
    | spl13_7
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f443,f231,f189,f561])).

fof(f443,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(X1,sK2,X0)
        | ~ m1_yellow_0(sK1,X1)
        | ~ l1_orders_2(X1)
        | v2_struct_0(X1) )
    | ~ spl13_7
    | ~ spl13_18 ),
    inference(subsumption_resolution,[],[f441,f190])).

fof(f441,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_lattice3(X1,sK2,X0)
        | ~ m1_yellow_0(sK1,X1)
        | v2_struct_0(sK1)
        | ~ l1_orders_2(X1)
        | v2_struct_0(X1) )
    | ~ spl13_18 ),
    inference(resolution,[],[f436,f232])).

fof(f549,plain,
    ( spl13_80
    | spl13_1
    | ~ spl13_4
    | spl13_7
    | ~ spl13_12
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f416,f217,f210,f189,f182,f168,f547])).

fof(f416,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,X0,X1) )
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f415,f169])).

fof(f415,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f414,f183])).

fof(f414,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,X0,X1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_7
    | ~ spl13_12
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f413,f190])).

fof(f413,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | r2_lattice3(sK1,X0,X1)
        | v2_struct_0(sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_12
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f412,f218])).

fof(f412,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_yellow_0(sK1,sK0)
        | r2_lattice3(sK1,X0,X1)
        | v2_struct_0(sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_12 ),
    inference(resolution,[],[f411,f211])).

fof(f531,plain,
    ( spl13_74
    | ~ spl13_44
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f512,f507,f344,f529])).

fof(f512,plain,
    ( m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK0))
    | ~ spl13_44
    | ~ spl13_72 ),
    inference(resolution,[],[f508,f345])).

fof(f509,plain,
    ( spl13_72
    | spl13_1
    | ~ spl13_4
    | spl13_7
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f314,f217,f189,f182,f168,f507])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_1
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f313,f169])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f312,f183])).

fof(f312,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_7
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f309,f190])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl13_14 ),
    inference(resolution,[],[f135,f218])).

fof(f346,plain,
    ( spl13_44
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f242,f238,f344])).

fof(f242,plain,
    ( m1_subset_1(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_20 ),
    inference(resolution,[],[f142,f239])).

fof(f299,plain,
    ( ~ spl13_33
    | ~ spl13_35 ),
    inference(avatar_split_clause,[],[f102,f297,f291])).

fof(f102,plain,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
    | ~ r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
      | ~ r1_yellow_0(sK1,sK2) )
    & r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    & r1_yellow_0(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_yellow_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f70,f69,f68])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                  | ~ r1_yellow_0(X1,X2) )
                & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                & r1_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(sK0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(sK0,X2),u1_struct_0(X1))
              & r1_yellow_0(sK0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k1_yellow_0(sK1,X2) != k1_yellow_0(X0,X2)
              | ~ r1_yellow_0(sK1,X2) )
            & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(sK1))
            & r1_yellow_0(X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_yellow_0(sK1,X0)
        & v4_yellow_0(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
            | ~ r1_yellow_0(X1,X2) )
          & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
          & r1_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( k1_yellow_0(X0,sK2) != k1_yellow_0(X1,sK2)
          | ~ r1_yellow_0(X1,sK2) )
        & r2_hidden(k1_yellow_0(X0,sK2),u1_struct_0(X1))
        & r1_yellow_0(X0,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                    & r1_yellow_0(X0,X2) )
                 => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                    & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',t65_yellow_0)).

fof(f267,plain,
    ( spl13_26
    | ~ spl13_14
    | ~ spl13_24 ),
    inference(avatar_split_clause,[],[f256,f253,f217,f265])).

fof(f253,plain,
    ( spl13_24
  <=> ! [X0] :
        ( ~ m1_yellow_0(X0,sK0)
        | l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f256,plain,
    ( l1_orders_2(sK1)
    | ~ spl13_14
    | ~ spl13_24 ),
    inference(resolution,[],[f254,f218])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ m1_yellow_0(X0,sK0)
        | l1_orders_2(X0) )
    | ~ spl13_24 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl13_24
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f250,f182,f253])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_yellow_0(X0,sK0)
        | l1_orders_2(X0) )
    | ~ spl13_4 ),
    inference(resolution,[],[f105,f183])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_yellow_0(X1,X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t65_yellow_0.p',dt_m1_yellow_0)).

fof(f240,plain,(
    spl13_20 ),
    inference(avatar_split_clause,[],[f101,f238])).

fof(f101,plain,(
    r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f71])).

fof(f233,plain,(
    spl13_18 ),
    inference(avatar_split_clause,[],[f99,f231])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f71])).

fof(f226,plain,(
    spl13_16 ),
    inference(avatar_split_clause,[],[f100,f224])).

fof(f100,plain,(
    r1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f71])).

fof(f219,plain,(
    spl13_14 ),
    inference(avatar_split_clause,[],[f98,f217])).

fof(f98,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f212,plain,(
    spl13_12 ),
    inference(avatar_split_clause,[],[f97,f210])).

fof(f97,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f191,plain,(
    ~ spl13_7 ),
    inference(avatar_split_clause,[],[f96,f189])).

fof(f96,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

fof(f184,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f95,f182])).

fof(f95,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f177,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f94,f175])).

fof(f94,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f170,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f93,f168])).

fof(f93,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
