%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1165+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:10 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 269 expanded)
%              Number of leaves         :   20 ( 123 expanded)
%              Depth                    :   12
%              Number of atoms          :  530 (1698 expanded)
%              Number of equality atoms :   69 ( 303 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2898,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2294,f2299,f2304,f2309,f2314,f2324,f2333,f2334,f2341,f2542,f2602,f2641,f2674,f2897])).

fof(f2897,plain,
    ( spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | ~ spl34_20
    | ~ spl34_23
    | ~ spl34_26 ),
    inference(avatar_contradiction_clause,[],[f2896])).

fof(f2896,plain,
    ( $false
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | ~ spl34_20
    | ~ spl34_23
    | ~ spl34_26 ),
    inference(subsumption_resolution,[],[f2895,f2601])).

fof(f2601,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ spl34_20 ),
    inference(avatar_component_clause,[],[f2599])).

fof(f2599,plain,
    ( spl34_20
  <=> r2_hidden(sK3(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_20])])).

fof(f2895,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | ~ spl34_23
    | ~ spl34_26 ),
    inference(forward_demodulation,[],[f2889,f2673])).

fof(f2673,plain,
    ( sK1 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK1))
    | ~ spl34_26 ),
    inference(avatar_component_clause,[],[f2671])).

fof(f2671,plain,
    ( spl34_26
  <=> sK1 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_26])])).

fof(f2889,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK1)))
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | ~ spl34_23 ),
    inference(unit_resulting_resolution,[],[f2293,f2298,f2303,f2308,f2313,f2640,f2323,f2152])).

fof(f2152,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1960])).

fof(f1960,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1959])).

fof(f1959,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1921])).

fof(f1921,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).

fof(f2323,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl34_7 ),
    inference(avatar_component_clause,[],[f2321])).

fof(f2321,plain,
    ( spl34_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_7])])).

fof(f2640,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl34_23 ),
    inference(avatar_component_clause,[],[f2638])).

fof(f2638,plain,
    ( spl34_23
  <=> m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_23])])).

fof(f2313,plain,
    ( l1_orders_2(sK0)
    | ~ spl34_5 ),
    inference(avatar_component_clause,[],[f2311])).

fof(f2311,plain,
    ( spl34_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_5])])).

fof(f2308,plain,
    ( v5_orders_2(sK0)
    | ~ spl34_4 ),
    inference(avatar_component_clause,[],[f2306])).

fof(f2306,plain,
    ( spl34_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_4])])).

fof(f2303,plain,
    ( v4_orders_2(sK0)
    | ~ spl34_3 ),
    inference(avatar_component_clause,[],[f2301])).

fof(f2301,plain,
    ( spl34_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_3])])).

fof(f2298,plain,
    ( v3_orders_2(sK0)
    | ~ spl34_2 ),
    inference(avatar_component_clause,[],[f2296])).

fof(f2296,plain,
    ( spl34_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_2])])).

fof(f2293,plain,
    ( ~ v2_struct_0(sK0)
    | spl34_1 ),
    inference(avatar_component_clause,[],[f2291])).

fof(f2291,plain,
    ( spl34_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_1])])).

fof(f2674,plain,
    ( spl34_26
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | spl34_8
    | ~ spl34_9 ),
    inference(avatar_split_clause,[],[f2468,f2330,f2326,f2321,f2311,f2306,f2301,f2296,f2291,f2671])).

fof(f2326,plain,
    ( spl34_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_8])])).

fof(f2330,plain,
    ( spl34_9
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_9])])).

fof(f2468,plain,
    ( sK1 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK1))
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | spl34_8
    | ~ spl34_9 ),
    inference(unit_resulting_resolution,[],[f2293,f2298,f2303,f2308,f2313,f2331,f2328,f2323,f2286])).

fof(f2286,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2121,f2118])).

fof(f2118,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1934])).

fof(f1934,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1933])).

fof(f1933,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1881])).

fof(f1881,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f2121,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2050])).

fof(f2050,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
                        & r2_hidden(sK3(X0,X1,X2),X1)
                        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2048,f2049])).

fof(f2049,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2048,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f2047])).

fof(f2047,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f1936])).

fof(f1936,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1935])).

fof(f1935,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1868])).

fof(f1868,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f2328,plain,
    ( k1_xboole_0 != sK1
    | spl34_8 ),
    inference(avatar_component_clause,[],[f2326])).

fof(f2331,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl34_9 ),
    inference(avatar_component_clause,[],[f2330])).

fof(f2641,plain,
    ( spl34_23
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | spl34_8
    | ~ spl34_9 ),
    inference(avatar_split_clause,[],[f2462,f2330,f2326,f2321,f2311,f2306,f2301,f2296,f2291,f2638])).

fof(f2462,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | spl34_8
    | ~ spl34_9 ),
    inference(unit_resulting_resolution,[],[f2293,f2298,f2303,f2308,f2313,f2331,f2328,f2323,f2288])).

fof(f2288,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2119,f2118])).

fof(f2119,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2050])).

fof(f2602,plain,
    ( spl34_20
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | spl34_8
    | ~ spl34_9 ),
    inference(avatar_split_clause,[],[f2461,f2330,f2326,f2321,f2311,f2306,f2301,f2296,f2291,f2599])).

fof(f2461,plain,
    ( r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5
    | ~ spl34_7
    | spl34_8
    | ~ spl34_9 ),
    inference(unit_resulting_resolution,[],[f2293,f2298,f2303,f2308,f2313,f2331,f2328,f2323,f2287])).

fof(f2287,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f2120,f2118])).

fof(f2120,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2050])).

fof(f2542,plain,
    ( spl34_10
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5 ),
    inference(avatar_split_clause,[],[f2399,f2311,f2306,f2301,f2296,f2291,f2338])).

fof(f2338,plain,
    ( spl34_10
  <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl34_10])])).

fof(f2399,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl34_1
    | ~ spl34_2
    | ~ spl34_3
    | ~ spl34_4
    | ~ spl34_5 ),
    inference(unit_resulting_resolution,[],[f2293,f2298,f2303,f2308,f2313,f2144,f2284])).

fof(f2284,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f2250])).

fof(f2250,plain,(
    ! [X0] :
      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f2249])).

fof(f2249,plain,(
    ! [X0,X1] :
      ( m1_orders_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f2124])).

fof(f2124,plain,(
    ! [X2,X0,X1] :
      ( m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2050])).

fof(f2144,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f2341,plain,
    ( ~ spl34_10
    | ~ spl34_8
    | spl34_9 ),
    inference(avatar_split_clause,[],[f2335,f2330,f2326,f2338])).

fof(f2335,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl34_8
    | spl34_9 ),
    inference(backward_demodulation,[],[f2332,f2327])).

fof(f2327,plain,
    ( k1_xboole_0 = sK1
    | ~ spl34_8 ),
    inference(avatar_component_clause,[],[f2326])).

fof(f2332,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | spl34_9 ),
    inference(avatar_component_clause,[],[f2330])).

fof(f2334,plain,
    ( spl34_9
    | spl34_8 ),
    inference(avatar_split_clause,[],[f2116,f2326,f2330])).

fof(f2116,plain,
    ( k1_xboole_0 = sK1
    | m1_orders_2(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f2044])).

fof(f2044,plain,
    ( ( ( k1_xboole_0 = sK1
        & ~ m1_orders_2(sK1,sK0,sK1) )
      | ( m1_orders_2(sK1,sK0,sK1)
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1930,f2043,f2042])).

fof(f2042,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
              | ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,sK0,X1) )
            | ( m1_orders_2(X1,sK0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2043,plain,
    ( ? [X1] :
        ( ( ( k1_xboole_0 = X1
            & ~ m1_orders_2(X1,sK0,X1) )
          | ( m1_orders_2(X1,sK0,X1)
            & k1_xboole_0 != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ( k1_xboole_0 = sK1
          & ~ m1_orders_2(sK1,sK0,sK1) )
        | ( m1_orders_2(sK1,sK0,sK1)
          & k1_xboole_0 != sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f1930,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1929])).

fof(f1929,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1926])).

fof(f1926,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k1_xboole_0 = X1
                  & ~ m1_orders_2(X1,X0,X1) )
              & ~ ( m1_orders_2(X1,X0,X1)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1925])).

fof(f1925,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

fof(f2333,plain,
    ( ~ spl34_8
    | ~ spl34_9 ),
    inference(avatar_split_clause,[],[f2113,f2330,f2326])).

fof(f2113,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f2044])).

fof(f2324,plain,(
    spl34_7 ),
    inference(avatar_split_clause,[],[f2112,f2321])).

fof(f2112,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2044])).

fof(f2314,plain,(
    spl34_5 ),
    inference(avatar_split_clause,[],[f2111,f2311])).

fof(f2111,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2044])).

fof(f2309,plain,(
    spl34_4 ),
    inference(avatar_split_clause,[],[f2110,f2306])).

fof(f2110,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2044])).

fof(f2304,plain,(
    spl34_3 ),
    inference(avatar_split_clause,[],[f2109,f2301])).

fof(f2109,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2044])).

fof(f2299,plain,(
    spl34_2 ),
    inference(avatar_split_clause,[],[f2108,f2296])).

fof(f2108,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f2044])).

fof(f2294,plain,(
    ~ spl34_1 ),
    inference(avatar_split_clause,[],[f2107,f2291])).

fof(f2107,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2044])).
%------------------------------------------------------------------------------
