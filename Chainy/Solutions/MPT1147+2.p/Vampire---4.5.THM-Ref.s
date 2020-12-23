%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1147+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:09 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 524 expanded)
%              Number of leaves         :   26 ( 223 expanded)
%              Depth                    :   11
%              Number of atoms          :  873 (4787 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2765,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2289,f2294,f2299,f2304,f2309,f2352,f2353,f2354,f2360,f2371,f2375,f2376,f2545,f2555,f2586,f2597,f2599,f2647,f2696,f2707,f2711,f2713,f2715,f2762,f2764])).

fof(f2764,plain,
    ( ~ spl42_1
    | ~ spl42_3
    | ~ spl42_9
    | spl42_11
    | ~ spl42_13
    | ~ spl42_14
    | ~ spl42_16
    | spl42_49 ),
    inference(avatar_contradiction_clause,[],[f2763])).

fof(f2763,plain,
    ( $false
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_9
    | spl42_11
    | ~ spl42_13
    | ~ spl42_14
    | ~ spl42_16
    | spl42_49 ),
    inference(subsumption_resolution,[],[f2694,f2625])).

fof(f2625,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_9
    | spl42_11
    | ~ spl42_13
    | ~ spl42_14
    | ~ spl42_16 ),
    inference(unit_resulting_resolution,[],[f2288,f2298,f2346,f2336,f2351,f2328,f2364,f2284])).

fof(f2284,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X4,X0)
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f2283,f2114])).

fof(f2114,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f1916])).

fof(f1916,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1915])).

fof(f1915,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f2283,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X4,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f2131,f2114])).

fof(f2131,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X1)
      | r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,X4)
      | ~ r2_hidden(X1,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X4,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2034,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( r2_hidden(X2,sK9(X0,X1,X2))
                    & r2_hidden(X1,sK9(X0,X1,X2))
                    & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(sK9(X0,X1,X2),X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f1930,f2033])).

fof(f2033,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
     => ( r2_hidden(X2,sK9(X0,X1,X2))
        & r2_hidden(X1,sK9(X0,X1,X2))
        & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v6_orders_2(sK9(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1930,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f1929])).

fof(f1929,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1899])).

fof(f1899,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f1895])).

fof(f1895,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

fof(f2364,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl42_16 ),
    inference(avatar_component_clause,[],[f2362])).

fof(f2362,plain,
    ( spl42_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_16])])).

fof(f2328,plain,
    ( v6_orders_2(sK3,sK0)
    | ~ spl42_9 ),
    inference(avatar_component_clause,[],[f2326])).

fof(f2326,plain,
    ( spl42_9
  <=> v6_orders_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_9])])).

fof(f2351,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl42_14 ),
    inference(avatar_component_clause,[],[f2349])).

fof(f2349,plain,
    ( spl42_14
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_14])])).

fof(f2336,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl42_11 ),
    inference(avatar_component_clause,[],[f2334])).

fof(f2334,plain,
    ( spl42_11
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_11])])).

fof(f2346,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl42_13 ),
    inference(avatar_component_clause,[],[f2344])).

fof(f2344,plain,
    ( spl42_13
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_13])])).

fof(f2298,plain,
    ( l1_orders_2(sK0)
    | ~ spl42_3 ),
    inference(avatar_component_clause,[],[f2296])).

fof(f2296,plain,
    ( spl42_3
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_3])])).

fof(f2288,plain,
    ( v3_orders_2(sK0)
    | ~ spl42_1 ),
    inference(avatar_component_clause,[],[f2286])).

fof(f2286,plain,
    ( spl42_1
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_1])])).

fof(f2694,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl42_49 ),
    inference(avatar_component_clause,[],[f2693])).

fof(f2693,plain,
    ( spl42_49
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_49])])).

fof(f2762,plain,
    ( ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_10
    | spl42_11
    | ~ spl42_49 ),
    inference(avatar_contradiction_clause,[],[f2761])).

fof(f2761,plain,
    ( $false
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_10
    | spl42_11
    | ~ spl42_49 ),
    inference(subsumption_resolution,[],[f2752,f2731])).

fof(f2731,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_10
    | spl42_11
    | ~ spl42_49 ),
    inference(backward_demodulation,[],[f2336,f2728])).

fof(f2728,plain,
    ( sK1 = sK2
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_10
    | ~ spl42_49 ),
    inference(unit_resulting_resolution,[],[f2298,f2303,f2308,f2695,f2332,f2109])).

fof(f2109,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2017])).

fof(f2017,plain,(
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
    inference(flattening,[],[f2016])).

fof(f2016,plain,(
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
    inference(nnf_transformation,[],[f1910])).

fof(f1910,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1863])).

fof(f1863,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f2332,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | spl42_10 ),
    inference(avatar_component_clause,[],[f2330])).

fof(f2330,plain,
    ( spl42_10
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_10])])).

fof(f2695,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl42_49 ),
    inference(avatar_component_clause,[],[f2693])).

fof(f2308,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl42_5 ),
    inference(avatar_component_clause,[],[f2306])).

fof(f2306,plain,
    ( spl42_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_5])])).

fof(f2303,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl42_4 ),
    inference(avatar_component_clause,[],[f2301])).

fof(f2301,plain,
    ( spl42_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_4])])).

fof(f2752,plain,
    ( r1_orders_2(sK0,sK1,sK1)
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_10
    | ~ spl42_49 ),
    inference(backward_demodulation,[],[f2695,f2728])).

fof(f2715,plain,
    ( ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_37
    | ~ spl42_49 ),
    inference(avatar_contradiction_clause,[],[f2714])).

fof(f2714,plain,
    ( $false
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_37
    | ~ spl42_49 ),
    inference(subsumption_resolution,[],[f2543,f2699])).

fof(f2699,plain,
    ( v6_orders_2(sK9(sK0,sK2,sK1),sK0)
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_49 ),
    inference(unit_resulting_resolution,[],[f2288,f2298,f2308,f2303,f2695,f2133])).

fof(f2133,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v6_orders_2(sK9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2543,plain,
    ( ~ v6_orders_2(sK9(sK0,sK2,sK1),sK0)
    | spl42_37 ),
    inference(avatar_component_clause,[],[f2542])).

fof(f2542,plain,
    ( spl42_37
  <=> v6_orders_2(sK9(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_37])])).

fof(f2713,plain,
    ( ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_39
    | ~ spl42_49 ),
    inference(avatar_contradiction_clause,[],[f2712])).

fof(f2712,plain,
    ( $false
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_39
    | ~ spl42_49 ),
    inference(subsumption_resolution,[],[f2553,f2703])).

fof(f2703,plain,
    ( r2_hidden(sK2,sK9(sK0,sK2,sK1))
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_49 ),
    inference(unit_resulting_resolution,[],[f2288,f2298,f2308,f2303,f2695,f2137])).

fof(f2137,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,sK9(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2553,plain,
    ( ~ r2_hidden(sK2,sK9(sK0,sK2,sK1))
    | spl42_39 ),
    inference(avatar_component_clause,[],[f2552])).

fof(f2552,plain,
    ( spl42_39
  <=> r2_hidden(sK2,sK9(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_39])])).

fof(f2711,plain,
    ( ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_42
    | ~ spl42_49 ),
    inference(avatar_contradiction_clause,[],[f2710])).

fof(f2710,plain,
    ( $false
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | spl42_42
    | ~ spl42_49 ),
    inference(subsumption_resolution,[],[f2584,f2705])).

fof(f2705,plain,
    ( r2_hidden(sK1,sK9(sK0,sK2,sK1))
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_49 ),
    inference(unit_resulting_resolution,[],[f2288,f2298,f2308,f2303,f2695,f2139])).

fof(f2139,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X2,sK9(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2584,plain,
    ( ~ r2_hidden(sK1,sK9(sK0,sK2,sK1))
    | spl42_42 ),
    inference(avatar_component_clause,[],[f2583])).

fof(f2583,plain,
    ( spl42_42
  <=> r2_hidden(sK1,sK9(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_42])])).

fof(f2707,plain,
    ( ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_18
    | ~ spl42_37
    | ~ spl42_39
    | ~ spl42_42
    | ~ spl42_49 ),
    inference(avatar_contradiction_clause,[],[f2706])).

fof(f2706,plain,
    ( $false
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_18
    | ~ spl42_37
    | ~ spl42_39
    | ~ spl42_42
    | ~ spl42_49 ),
    inference(subsumption_resolution,[],[f2701,f2587])).

fof(f2587,plain,
    ( ~ m1_subset_1(sK9(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl42_18
    | ~ spl42_37
    | ~ spl42_39
    | ~ spl42_42 ),
    inference(unit_resulting_resolution,[],[f2544,f2554,f2585,f2374])).

fof(f2374,plain,
    ( ! [X3] :
        ( ~ v6_orders_2(X3,sK0)
        | ~ r2_hidden(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3) )
    | ~ spl42_18 ),
    inference(avatar_component_clause,[],[f2373])).

fof(f2373,plain,
    ( spl42_18
  <=> ! [X3] :
        ( ~ r2_hidden(sK2,X3)
        | ~ v6_orders_2(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_18])])).

fof(f2585,plain,
    ( r2_hidden(sK1,sK9(sK0,sK2,sK1))
    | ~ spl42_42 ),
    inference(avatar_component_clause,[],[f2583])).

fof(f2554,plain,
    ( r2_hidden(sK2,sK9(sK0,sK2,sK1))
    | ~ spl42_39 ),
    inference(avatar_component_clause,[],[f2552])).

fof(f2544,plain,
    ( v6_orders_2(sK9(sK0,sK2,sK1),sK0)
    | ~ spl42_37 ),
    inference(avatar_component_clause,[],[f2542])).

fof(f2701,plain,
    ( m1_subset_1(sK9(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_49 ),
    inference(unit_resulting_resolution,[],[f2288,f2298,f2308,f2303,f2695,f2135])).

fof(f2135,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2696,plain,
    ( spl42_49
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_10 ),
    inference(avatar_split_clause,[],[f2617,f2330,f2306,f2301,f2296,f2693])).

fof(f2617,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_10 ),
    inference(unit_resulting_resolution,[],[f2298,f2303,f2308,f2331,f2107])).

fof(f2107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2017])).

fof(f2331,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl42_10 ),
    inference(avatar_component_clause,[],[f2330])).

fof(f2647,plain,
    ( ~ spl42_14
    | ~ spl42_9
    | ~ spl42_13
    | ~ spl42_16
    | ~ spl42_18 ),
    inference(avatar_split_clause,[],[f2634,f2373,f2362,f2344,f2326,f2349])).

fof(f2634,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl42_9
    | ~ spl42_13
    | ~ spl42_16
    | ~ spl42_18 ),
    inference(unit_resulting_resolution,[],[f2346,f2328,f2364,f2374])).

fof(f2599,plain,
    ( ~ spl42_2
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_10
    | ~ spl42_11 ),
    inference(avatar_contradiction_clause,[],[f2598])).

fof(f2598,plain,
    ( $false
    | ~ spl42_2
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_10
    | ~ spl42_11 ),
    inference(subsumption_resolution,[],[f2331,f2422])).

fof(f2422,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl42_2
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11 ),
    inference(unit_resulting_resolution,[],[f2293,f2298,f2308,f2335,f2303,f2105])).

fof(f2105,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f1907])).

fof(f1907,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f1906])).

fof(f1906,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1890])).

fof(f1890,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

fof(f2335,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl42_11 ),
    inference(avatar_component_clause,[],[f2334])).

fof(f2293,plain,
    ( v5_orders_2(sK0)
    | ~ spl42_2 ),
    inference(avatar_component_clause,[],[f2291])).

fof(f2291,plain,
    ( spl42_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl42_2])])).

fof(f2597,plain,
    ( ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11
    | ~ spl42_18
    | ~ spl42_37
    | ~ spl42_39
    | ~ spl42_42 ),
    inference(avatar_contradiction_clause,[],[f2596])).

fof(f2596,plain,
    ( $false
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11
    | ~ spl42_18
    | ~ spl42_37
    | ~ spl42_39
    | ~ spl42_42 ),
    inference(subsumption_resolution,[],[f2587,f2444])).

fof(f2444,plain,
    ( m1_subset_1(sK9(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11 ),
    inference(unit_resulting_resolution,[],[f2288,f2298,f2308,f2335,f2303,f2134])).

fof(f2134,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2586,plain,
    ( spl42_42
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11 ),
    inference(avatar_split_clause,[],[f2437,f2334,f2306,f2301,f2296,f2286,f2583])).

fof(f2437,plain,
    ( r2_hidden(sK1,sK9(sK0,sK2,sK1))
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11 ),
    inference(unit_resulting_resolution,[],[f2288,f2298,f2308,f2335,f2303,f2138])).

fof(f2138,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X2,sK9(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2555,plain,
    ( spl42_39
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11 ),
    inference(avatar_split_clause,[],[f2435,f2334,f2306,f2301,f2296,f2286,f2552])).

fof(f2435,plain,
    ( r2_hidden(sK2,sK9(sK0,sK2,sK1))
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11 ),
    inference(unit_resulting_resolution,[],[f2288,f2298,f2308,f2335,f2303,f2136])).

fof(f2136,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,sK9(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2545,plain,
    ( spl42_37
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11 ),
    inference(avatar_split_clause,[],[f2428,f2334,f2306,f2301,f2296,f2286,f2542])).

fof(f2428,plain,
    ( v6_orders_2(sK9(sK0,sK2,sK1),sK0)
    | ~ spl42_1
    | ~ spl42_3
    | ~ spl42_4
    | ~ spl42_5
    | ~ spl42_11 ),
    inference(unit_resulting_resolution,[],[f2288,f2298,f2308,f2335,f2303,f2132])).

fof(f2132,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v6_orders_2(sK9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f2034])).

fof(f2376,plain,
    ( spl42_18
    | ~ spl42_10
    | spl42_11 ),
    inference(avatar_split_clause,[],[f2102,f2334,f2330,f2373])).

fof(f2102,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK2,sK1)
      | ~ r2_orders_2(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X3,sK0) ) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2015,plain,
    ( ( ( ( r1_orders_2(sK0,sK2,sK1)
          | ~ r2_orders_2(sK0,sK1,sK2) )
        & ( ~ r1_orders_2(sK0,sK2,sK1)
          | r2_orders_2(sK0,sK1,sK2) ) )
      | ! [X3] :
          ( ~ r2_hidden(sK2,X3)
          | ~ r2_hidden(sK1,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v6_orders_2(X3,sK0) ) )
    & ( ( ( r2_orders_2(sK0,sK1,sK2)
          | r1_orders_2(sK0,sK2,sK1) )
        & ( ~ r1_orders_2(sK0,sK2,sK1)
          | ~ r2_orders_2(sK0,sK1,sK2) ) )
      | ( r2_hidden(sK2,sK3)
        & r2_hidden(sK1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(sK3,sK0) ) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2010,f2014,f2013,f2012,f2011])).

fof(f2011,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ( r1_orders_2(X0,X2,X1)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X1)
                      | r2_orders_2(X0,X1,X2) ) )
                  | ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) ) )
                & ( ( ( r2_orders_2(X0,X1,X2)
                      | r1_orders_2(X0,X2,X1) )
                    & ( ~ r1_orders_2(X0,X2,X1)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ? [X4] :
                      ( r2_hidden(X2,X4)
                      & r2_hidden(X1,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X4,X0) ) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(sK0,X2,X1)
                    | ~ r2_orders_2(sK0,X1,X2) )
                  & ( ~ r1_orders_2(sK0,X2,X1)
                    | r2_orders_2(sK0,X1,X2) ) )
                | ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                    | ~ v6_orders_2(X3,sK0) ) )
              & ( ( ( r2_orders_2(sK0,X1,X2)
                    | r1_orders_2(sK0,X2,X1) )
                  & ( ~ r1_orders_2(sK0,X2,X1)
                    | ~ r2_orders_2(sK0,X1,X2) ) )
                | ? [X4] :
                    ( r2_hidden(X2,X4)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                    & v6_orders_2(X4,sK0) ) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2012,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ( r1_orders_2(sK0,X2,X1)
                  | ~ r2_orders_2(sK0,X1,X2) )
                & ( ~ r1_orders_2(sK0,X2,X1)
                  | r2_orders_2(sK0,X1,X2) ) )
              | ! [X3] :
                  ( ~ r2_hidden(X2,X3)
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                  | ~ v6_orders_2(X3,sK0) ) )
            & ( ( ( r2_orders_2(sK0,X1,X2)
                  | r1_orders_2(sK0,X2,X1) )
                & ( ~ r1_orders_2(sK0,X2,X1)
                  | ~ r2_orders_2(sK0,X1,X2) ) )
              | ? [X4] :
                  ( r2_hidden(X2,X4)
                  & r2_hidden(X1,X4)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                  & v6_orders_2(X4,sK0) ) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ( ( r1_orders_2(sK0,X2,sK1)
                | ~ r2_orders_2(sK0,sK1,X2) )
              & ( ~ r1_orders_2(sK0,X2,sK1)
                | r2_orders_2(sK0,sK1,X2) ) )
            | ! [X3] :
                ( ~ r2_hidden(X2,X3)
                | ~ r2_hidden(sK1,X3)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
                | ~ v6_orders_2(X3,sK0) ) )
          & ( ( ( r2_orders_2(sK0,sK1,X2)
                | r1_orders_2(sK0,X2,sK1) )
              & ( ~ r1_orders_2(sK0,X2,sK1)
                | ~ r2_orders_2(sK0,sK1,X2) ) )
            | ? [X4] :
                ( r2_hidden(X2,X4)
                & r2_hidden(sK1,X4)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
                & v6_orders_2(X4,sK0) ) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2013,plain,
    ( ? [X2] :
        ( ( ( ( r1_orders_2(sK0,X2,sK1)
              | ~ r2_orders_2(sK0,sK1,X2) )
            & ( ~ r1_orders_2(sK0,X2,sK1)
              | r2_orders_2(sK0,sK1,X2) ) )
          | ! [X3] :
              ( ~ r2_hidden(X2,X3)
              | ~ r2_hidden(sK1,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
              | ~ v6_orders_2(X3,sK0) ) )
        & ( ( ( r2_orders_2(sK0,sK1,X2)
              | r1_orders_2(sK0,X2,sK1) )
            & ( ~ r1_orders_2(sK0,X2,sK1)
              | ~ r2_orders_2(sK0,sK1,X2) ) )
          | ? [X4] :
              ( r2_hidden(X2,X4)
              & r2_hidden(sK1,X4)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
              & v6_orders_2(X4,sK0) ) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ( ( r1_orders_2(sK0,sK2,sK1)
            | ~ r2_orders_2(sK0,sK1,sK2) )
          & ( ~ r1_orders_2(sK0,sK2,sK1)
            | r2_orders_2(sK0,sK1,sK2) ) )
        | ! [X3] :
            ( ~ r2_hidden(sK2,X3)
            | ~ r2_hidden(sK1,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(X3,sK0) ) )
      & ( ( ( r2_orders_2(sK0,sK1,sK2)
            | r1_orders_2(sK0,sK2,sK1) )
          & ( ~ r1_orders_2(sK0,sK2,sK1)
            | ~ r2_orders_2(sK0,sK1,sK2) ) )
        | ? [X4] :
            ( r2_hidden(sK2,X4)
            & r2_hidden(sK1,X4)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
            & v6_orders_2(X4,sK0) ) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f2014,plain,
    ( ? [X4] :
        ( r2_hidden(sK2,X4)
        & r2_hidden(sK1,X4)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(X4,sK0) )
   => ( r2_hidden(sK2,sK3)
      & r2_hidden(sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      & v6_orders_2(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2010,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | r2_orders_2(X0,X1,X2) ) )
                | ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v6_orders_2(X3,X0) ) )
              & ( ( ( r2_orders_2(X0,X1,X2)
                    | r1_orders_2(X0,X2,X1) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) ) )
                | ? [X4] :
                    ( r2_hidden(X2,X4)
                    & r2_hidden(X1,X4)
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X4,X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f2009])).

fof(f2009,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | r2_orders_2(X0,X1,X2) ) )
                | ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v6_orders_2(X3,X0) ) )
              & ( ( ( r2_orders_2(X0,X1,X2)
                    | r1_orders_2(X0,X2,X1) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) ) )
                | ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f2008])).

fof(f2008,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ( r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | r2_orders_2(X0,X1,X2) ) )
                | ! [X3] :
                    ( ~ r2_hidden(X2,X3)
                    | ~ r2_hidden(X1,X3)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | ~ v6_orders_2(X3,X0) ) )
              & ( ( ( r2_orders_2(X0,X1,X2)
                    | r1_orders_2(X0,X2,X1) )
                  & ( ~ r1_orders_2(X0,X2,X1)
                    | ~ r2_orders_2(X0,X1,X2) ) )
                | ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f1901])).

fof(f1901,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f1900])).

fof(f1900,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1897])).

fof(f1897,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                <=> ( r2_orders_2(X0,X1,X2)
                  <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1896])).

fof(f1896,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <=> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_orders_2)).

fof(f2375,plain,
    ( spl42_18
    | spl42_10
    | ~ spl42_11 ),
    inference(avatar_split_clause,[],[f2101,f2334,f2330,f2373])).

fof(f2101,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,sK2,sK1)
      | r2_orders_2(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,X3)
      | ~ r2_hidden(sK1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(X3,sK0) ) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2371,plain,
    ( spl42_16
    | spl42_11
    | spl42_10 ),
    inference(avatar_split_clause,[],[f2098,f2330,f2334,f2362])).

fof(f2098,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2360,plain,
    ( spl42_14
    | spl42_11
    | spl42_10 ),
    inference(avatar_split_clause,[],[f2100,f2330,f2334,f2349])).

fof(f2100,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2354,plain,
    ( spl42_13
    | spl42_11
    | spl42_10 ),
    inference(avatar_split_clause,[],[f2099,f2330,f2334,f2344])).

fof(f2099,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2353,plain,
    ( spl42_9
    | spl42_11
    | spl42_10 ),
    inference(avatar_split_clause,[],[f2097,f2330,f2334,f2326])).

fof(f2097,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | v6_orders_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2352,plain,
    ( spl42_14
    | ~ spl42_10
    | ~ spl42_11 ),
    inference(avatar_split_clause,[],[f2096,f2334,f2330,f2349])).

fof(f2096,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2309,plain,(
    spl42_5 ),
    inference(avatar_split_clause,[],[f2092,f2306])).

fof(f2092,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2304,plain,(
    spl42_4 ),
    inference(avatar_split_clause,[],[f2091,f2301])).

fof(f2091,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2299,plain,(
    spl42_3 ),
    inference(avatar_split_clause,[],[f2090,f2296])).

fof(f2090,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2294,plain,(
    spl42_2 ),
    inference(avatar_split_clause,[],[f2089,f2291])).

fof(f2089,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2015])).

fof(f2289,plain,(
    spl42_1 ),
    inference(avatar_split_clause,[],[f2088,f2286])).

fof(f2088,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2015])).
%------------------------------------------------------------------------------
