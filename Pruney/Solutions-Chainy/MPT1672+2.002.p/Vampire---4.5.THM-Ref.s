%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:16 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 425 expanded)
%              Number of leaves         :   34 ( 150 expanded)
%              Depth                    :   15
%              Number of atoms          :  834 (2402 expanded)
%              Number of equality atoms :   34 ( 175 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1990,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f106,f132,f152,f155,f165,f222,f278,f283,f300,f329,f351,f366,f418,f430,f604,f671,f1504,f1529,f1555,f1701,f1973,f1989])).

fof(f1989,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | spl7_25
    | ~ spl7_26
    | ~ spl7_88
    | ~ spl7_97 ),
    inference(avatar_contradiction_clause,[],[f1988])).

fof(f1988,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | spl7_25
    | ~ spl7_26
    | ~ spl7_88
    | ~ spl7_97 ),
    inference(subsumption_resolution,[],[f1987,f350])).

fof(f350,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl7_25
  <=> r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f1987,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_26
    | ~ spl7_88
    | ~ spl7_97 ),
    inference(subsumption_resolution,[],[f1986,f105])).

fof(f105,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1986,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3)
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_88
    | ~ spl7_97 ),
    inference(resolution,[],[f1924,f1849])).

fof(f1849,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0) )
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f1597,f1690])).

fof(f1690,plain,
    ( r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f1689])).

fof(f1689,plain,
    ( spl7_88
  <=> r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f1597,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) )
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(superposition,[],[f142,f365])).

fof(f365,plain,
    ( sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl7_26
  <=> sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f140,f86])).

fof(f86,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f101,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f101,plain,
    ( ! [X25] : m1_subset_1(k1_yellow_0(sK0,X25),u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f1924,plain,
    ( r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f1923])).

fof(f1923,plain,
    ( spl7_97
  <=> r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f1973,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_23
    | spl7_97 ),
    inference(avatar_contradiction_clause,[],[f1972])).

fof(f1972,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_23
    | spl7_97 ),
    inference(subsumption_resolution,[],[f1971,f127])).

fof(f127,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_9
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1971,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_23
    | spl7_97 ),
    inference(resolution,[],[f1945,f299])).

fof(f299,plain,
    ( r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl7_23
  <=> r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1945,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1)
        | ~ r2_lattice3(sK0,X1,sK3) )
    | ~ spl7_4
    | ~ spl7_5
    | spl7_97 ),
    inference(subsumption_resolution,[],[f1941,f105])).

fof(f1941,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,sK3)
        | ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1) )
    | ~ spl7_4
    | spl7_97 ),
    inference(resolution,[],[f1925,f94])).

fof(f94,plain,
    ( ! [X10,X8,X9] :
        ( r2_lattice3(sK0,X8,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X9,X10)
        | ~ r1_tarski(X8,X9) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f1925,plain,
    ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | spl7_97 ),
    inference(avatar_component_clause,[],[f1923])).

fof(f1701,plain,
    ( ~ spl7_13
    | ~ spl7_22
    | spl7_88 ),
    inference(avatar_contradiction_clause,[],[f1700])).

fof(f1700,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_22
    | spl7_88 ),
    inference(subsumption_resolution,[],[f1699,f276])).

fof(f276,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl7_22
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f1699,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_13
    | spl7_88 ),
    inference(subsumption_resolution,[],[f1697,f164])).

fof(f164,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl7_13
  <=> r2_hidden(sK6(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f1697,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_88 ),
    inference(resolution,[],[f1691,f28])).

fof(f28,plain,(
    ! [X4] :
      ( r1_yellow_0(sK0,sK4(X4))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k1_yellow_0(X0,X4) = X3
                                    & r1_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r1_yellow_0(X0,X3) ) ) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X3)
                      <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k1_yellow_0(X0,X4) = X3
                                  & r1_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r1_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                    <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).

fof(f1691,plain,
    ( ~ r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | spl7_88 ),
    inference(avatar_component_clause,[],[f1689])).

fof(f1555,plain,
    ( ~ spl7_27
    | spl7_40
    | spl7_85 ),
    inference(avatar_contradiction_clause,[],[f1554])).

fof(f1554,plain,
    ( $false
    | ~ spl7_27
    | spl7_40
    | spl7_85 ),
    inference(subsumption_resolution,[],[f1553,f43])).

fof(f43,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f1553,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_27
    | spl7_40
    | spl7_85 ),
    inference(subsumption_resolution,[],[f1552,f602])).

fof(f602,plain,
    ( k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3))
    | spl7_40 ),
    inference(avatar_component_clause,[],[f601])).

fof(f601,plain,
    ( spl7_40
  <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f1552,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_27
    | spl7_85 ),
    inference(subsumption_resolution,[],[f1551,f417])).

fof(f417,plain,
    ( m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl7_27
  <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f1551,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_85 ),
    inference(resolution,[],[f1528,f34])).

fof(f34,plain,(
    ! [X6] :
      ( r1_yellow_0(sK0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X6
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1528,plain,
    ( ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_85 ),
    inference(avatar_component_clause,[],[f1526])).

fof(f1526,plain,
    ( spl7_85
  <=> r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f1529,plain,
    ( ~ spl7_85
    | ~ spl7_4
    | spl7_83 ),
    inference(avatar_split_clause,[],[f1511,f1501,f84,f1526])).

fof(f1501,plain,
    ( spl7_83
  <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f1511,plain,
    ( ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_4
    | spl7_83 ),
    inference(resolution,[],[f1503,f143])).

fof(f143,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2))
        | ~ r1_yellow_0(sK0,X2) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f141,f86])).

fof(f141,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1503,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | spl7_83 ),
    inference(avatar_component_clause,[],[f1501])).

fof(f1504,plain,
    ( ~ spl7_83
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_10
    | spl7_28
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f1348,f597,f427,f129,f103,f84,f79,f1501])).

fof(f79,plain,
    ( spl7_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f129,plain,
    ( spl7_10
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f427,plain,
    ( spl7_28
  <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f597,plain,
    ( spl7_39
  <=> r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f1348,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_10
    | spl7_28
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f1347,f101])).

fof(f1347,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_10
    | spl7_28
    | ~ spl7_39 ),
    inference(resolution,[],[f1341,f599])).

fof(f599,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f597])).

fof(f1341,plain,
    ( ! [X12] :
        ( ~ r2_hidden(X12,sK2)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X12) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_10
    | spl7_28 ),
    inference(resolution,[],[f830,f131])).

fof(f131,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f830,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,X1,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_28 ),
    inference(subsumption_resolution,[],[f829,f105])).

fof(f829,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_28 ),
    inference(duplicate_literal_removal,[],[f823])).

fof(f823,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_28 ),
    inference(resolution,[],[f438,f98])).

fof(f98,plain,
    ( ! [X19,X20,X18] :
        ( r1_orders_2(sK0,X19,X18)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ r2_hidden(X19,X20)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X20,X18) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f438,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK3)
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_28 ),
    inference(subsumption_resolution,[],[f433,f105])).

fof(f433,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4
    | spl7_28 ),
    inference(resolution,[],[f429,f188])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( r2_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_lattice3(sK0,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f88,f86])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_lattice3(sK0,X2,X0)
        | r2_lattice3(sK0,X2,X1) )
    | ~ spl7_3 ),
    inference(resolution,[],[f81,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r2_lattice3(X0,X3,X1)
      | r2_lattice3(X0,X3,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f81,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f429,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | spl7_28 ),
    inference(avatar_component_clause,[],[f427])).

fof(f671,plain,(
    ~ spl7_40 ),
    inference(avatar_contradiction_clause,[],[f670])).

fof(f670,plain,
    ( $false
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f660,f41])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f660,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_40 ),
    inference(superposition,[],[f42,f603])).

fof(f603,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f601])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f604,plain,
    ( spl7_39
    | spl7_40
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f425,f415,f601,f597])).

fof(f425,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f422,f43])).

fof(f422,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_27 ),
    inference(resolution,[],[f417,f33])).

fof(f33,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | k1_xboole_0 = X3
      | r2_hidden(k1_yellow_0(sK0,X3),sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f430,plain,
    ( ~ spl7_28
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(avatar_split_clause,[],[f371,f125,f103,f84,f427])).

fof(f371,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(subsumption_resolution,[],[f367,f105])).

fof(f367,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ spl7_4
    | spl7_9 ),
    inference(resolution,[],[f126,f255])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f254,f86])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f175,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f91,f100])).

fof(f100,plain,
    ( ! [X24,X23] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X24,X23),X23)
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | r2_lattice3(sK0,X24,X23) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(X3),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f126,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f418,plain,
    ( spl7_27
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f393,f219,f415])).

fof(f219,plain,
    ( spl7_18
  <=> r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f393,plain,
    ( m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_18 ),
    inference(resolution,[],[f221,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f221,plain,
    ( r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f219])).

fof(f366,plain,
    ( spl7_26
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f361,f275,f162,f363])).

fof(f361,plain,
    ( sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f166,f276])).

fof(f166,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_13 ),
    inference(resolution,[],[f164,f29])).

fof(f29,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k1_yellow_0(sK0,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f351,plain,
    ( ~ spl7_25
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_22
    | spl7_24 ),
    inference(avatar_split_clause,[],[f340,f326,f275,f103,f84,f348])).

fof(f326,plain,
    ( spl7_24
  <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f340,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_22
    | spl7_24 ),
    inference(subsumption_resolution,[],[f339,f105])).

fof(f339,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_22
    | spl7_24 ),
    inference(subsumption_resolution,[],[f334,f276])).

fof(f334,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_24 ),
    inference(resolution,[],[f328,f90])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,k1_tarski(X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | r2_lattice3(X0,k1_tarski(X2),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f328,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK2,sK3)),sK3)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f326])).

fof(f329,plain,
    ( ~ spl7_24
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10 ),
    inference(avatar_split_clause,[],[f322,f129,f103,f84,f326])).

fof(f322,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10 ),
    inference(subsumption_resolution,[],[f319,f105])).

fof(f319,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl7_4
    | spl7_10 ),
    inference(resolution,[],[f255,f130])).

fof(f130,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f300,plain,
    ( spl7_23
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f295,f271,f297])).

fof(f271,plain,
    ( spl7_21
  <=> m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f295,plain,
    ( r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)
    | ~ spl7_21 ),
    inference(resolution,[],[f273,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f273,plain,
    ( m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f271])).

fof(f283,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | spl7_10
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10
    | spl7_22 ),
    inference(subsumption_resolution,[],[f281,f130])).

fof(f281,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_22 ),
    inference(subsumption_resolution,[],[f280,f86])).

fof(f280,plain,
    ( ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_5
    | spl7_22 ),
    inference(subsumption_resolution,[],[f279,f105])).

fof(f279,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r2_lattice3(sK0,sK2,sK3)
    | spl7_22 ),
    inference(resolution,[],[f277,f56])).

fof(f277,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_22 ),
    inference(avatar_component_clause,[],[f275])).

fof(f278,plain,
    ( spl7_21
    | ~ spl7_22
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f167,f162,f275,f271])).

fof(f167,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_13 ),
    inference(resolution,[],[f164,f27])).

fof(f27,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f222,plain,
    ( spl7_18
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f217,f149,f219])).

fof(f149,plain,
    ( spl7_12
  <=> r2_hidden(sK6(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f217,plain,
    ( r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f151,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f151,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f165,plain,
    ( spl7_13
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10 ),
    inference(avatar_split_clause,[],[f160,f129,f103,f84,f162])).

fof(f160,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10 ),
    inference(subsumption_resolution,[],[f158,f105])).

fof(f158,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_10 ),
    inference(resolution,[],[f130,f99])).

fof(f99,plain,
    ( ! [X21,X22] :
        ( r2_lattice3(sK0,X22,X21)
        | r2_hidden(sK6(sK0,X22,X21),X22)
        | ~ m1_subset_1(X21,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f155,plain,
    ( ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f153,f127])).

fof(f153,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f31,f131])).

fof(f31,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f152,plain,
    ( spl7_12
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(avatar_split_clause,[],[f145,f125,f103,f84,f149])).

fof(f145,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(subsumption_resolution,[],[f144,f105])).

fof(f144,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_9 ),
    inference(resolution,[],[f99,f126])).

fof(f132,plain,
    ( spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f30,f129,f125])).

fof(f30,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f32,f103])).

fof(f32,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f40,f84])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f39,f79])).

fof(f39,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:24:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (28047)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (28059)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (28049)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (28051)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (28048)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (28064)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (28057)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (28055)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (28053)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.53  % (28052)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (28045)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28062)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (28063)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (28046)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (28044)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (28058)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.55  % (28050)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.55  % (28054)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.55  % (28060)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.55  % (28056)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (28061)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.68/0.58  % (28047)Refutation found. Thanks to Tanya!
% 1.68/0.58  % SZS status Theorem for theBenchmark
% 1.68/0.58  % SZS output start Proof for theBenchmark
% 1.68/0.58  fof(f1990,plain,(
% 1.68/0.58    $false),
% 1.68/0.58    inference(avatar_sat_refutation,[],[f82,f87,f106,f132,f152,f155,f165,f222,f278,f283,f300,f329,f351,f366,f418,f430,f604,f671,f1504,f1529,f1555,f1701,f1973,f1989])).
% 1.68/0.58  fof(f1989,plain,(
% 1.68/0.58    ~spl7_4 | ~spl7_5 | spl7_25 | ~spl7_26 | ~spl7_88 | ~spl7_97),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f1988])).
% 1.68/0.58  fof(f1988,plain,(
% 1.68/0.58    $false | (~spl7_4 | ~spl7_5 | spl7_25 | ~spl7_26 | ~spl7_88 | ~spl7_97)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1987,f350])).
% 1.68/0.58  fof(f350,plain,(
% 1.68/0.58    ~r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) | spl7_25),
% 1.68/0.58    inference(avatar_component_clause,[],[f348])).
% 1.68/0.58  fof(f348,plain,(
% 1.68/0.58    spl7_25 <=> r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.68/0.58  fof(f1987,plain,(
% 1.68/0.58    r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) | (~spl7_4 | ~spl7_5 | ~spl7_26 | ~spl7_88 | ~spl7_97)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1986,f105])).
% 1.68/0.58  fof(f105,plain,(
% 1.68/0.58    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl7_5),
% 1.68/0.58    inference(avatar_component_clause,[],[f103])).
% 1.68/0.58  fof(f103,plain,(
% 1.68/0.58    spl7_5 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.68/0.58  fof(f1986,plain,(
% 1.68/0.58    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) | (~spl7_4 | ~spl7_26 | ~spl7_88 | ~spl7_97)),
% 1.68/0.58    inference(resolution,[],[f1924,f1849])).
% 1.68/0.58  fof(f1849,plain,(
% 1.68/0.58    ( ! [X0] : (~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0)) ) | (~spl7_4 | ~spl7_26 | ~spl7_88)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1597,f1690])).
% 1.68/0.58  fof(f1690,plain,(
% 1.68/0.58    r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_88),
% 1.68/0.58    inference(avatar_component_clause,[],[f1689])).
% 1.68/0.58  fof(f1689,plain,(
% 1.68/0.58    spl7_88 <=> r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).
% 1.68/0.58  fof(f1597,plain,(
% 1.68/0.58    ( ! [X0] : (r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) | ~r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) ) | (~spl7_4 | ~spl7_26)),
% 1.68/0.58    inference(superposition,[],[f142,f365])).
% 1.68/0.58  fof(f365,plain,(
% 1.68/0.58    sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_26),
% 1.68/0.58    inference(avatar_component_clause,[],[f363])).
% 1.68/0.58  fof(f363,plain,(
% 1.68/0.58    spl7_26 <=> sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.68/0.58  fof(f142,plain,(
% 1.68/0.58    ( ! [X0,X1] : (r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | ~r1_yellow_0(sK0,X0)) ) | ~spl7_4),
% 1.68/0.58    inference(subsumption_resolution,[],[f140,f86])).
% 1.68/0.58  fof(f86,plain,(
% 1.68/0.58    l1_orders_2(sK0) | ~spl7_4),
% 1.68/0.58    inference(avatar_component_clause,[],[f84])).
% 1.68/0.58  fof(f84,plain,(
% 1.68/0.58    spl7_4 <=> l1_orders_2(sK0)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.68/0.58  fof(f140,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,X1) | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f101,f67])).
% 1.68/0.58  fof(f67,plain,(
% 1.68/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 1.68/0.58    inference(equality_resolution,[],[f53])).
% 1.68/0.58  fof(f53,plain,(
% 1.68/0.58    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 1.68/0.58    inference(cnf_transformation,[],[f20])).
% 1.68/0.58  fof(f20,plain,(
% 1.68/0.58    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.68/0.58    inference(flattening,[],[f19])).
% 1.68/0.58  fof(f19,plain,(
% 1.68/0.58    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.68/0.58    inference(ennf_transformation,[],[f7])).
% 1.68/0.58  fof(f7,axiom,(
% 1.68/0.58    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.68/0.58  fof(f101,plain,(
% 1.68/0.58    ( ! [X25] : (m1_subset_1(k1_yellow_0(sK0,X25),u1_struct_0(sK0))) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f86,f61])).
% 1.68/0.58  fof(f61,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f25])).
% 1.68/0.58  fof(f25,plain,(
% 1.68/0.58    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.68/0.58    inference(ennf_transformation,[],[f8])).
% 1.68/0.58  fof(f8,axiom,(
% 1.68/0.58    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.68/0.58  fof(f1924,plain,(
% 1.68/0.58    r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | ~spl7_97),
% 1.68/0.58    inference(avatar_component_clause,[],[f1923])).
% 1.68/0.58  fof(f1923,plain,(
% 1.68/0.58    spl7_97 <=> r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).
% 1.68/0.58  fof(f1973,plain,(
% 1.68/0.58    ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_23 | spl7_97),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f1972])).
% 1.68/0.58  fof(f1972,plain,(
% 1.68/0.58    $false | (~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_23 | spl7_97)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1971,f127])).
% 1.68/0.58  fof(f127,plain,(
% 1.68/0.58    r2_lattice3(sK0,sK1,sK3) | ~spl7_9),
% 1.68/0.58    inference(avatar_component_clause,[],[f125])).
% 1.68/0.58  fof(f125,plain,(
% 1.68/0.58    spl7_9 <=> r2_lattice3(sK0,sK1,sK3)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.68/0.58  fof(f1971,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,sK1,sK3) | (~spl7_4 | ~spl7_5 | ~spl7_23 | spl7_97)),
% 1.68/0.58    inference(resolution,[],[f1945,f299])).
% 1.68/0.58  fof(f299,plain,(
% 1.68/0.58    r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) | ~spl7_23),
% 1.68/0.58    inference(avatar_component_clause,[],[f297])).
% 1.68/0.58  fof(f297,plain,(
% 1.68/0.58    spl7_23 <=> r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.68/0.58  fof(f1945,plain,(
% 1.68/0.58    ( ! [X1] : (~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1) | ~r2_lattice3(sK0,X1,sK3)) ) | (~spl7_4 | ~spl7_5 | spl7_97)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1941,f105])).
% 1.68/0.58  fof(f1941,plain,(
% 1.68/0.58    ( ! [X1] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X1,sK3) | ~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1)) ) | (~spl7_4 | spl7_97)),
% 1.68/0.58    inference(resolution,[],[f1925,f94])).
% 1.68/0.58  fof(f94,plain,(
% 1.68/0.58    ( ! [X10,X8,X9] : (r2_lattice3(sK0,X8,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X9,X10) | ~r1_tarski(X8,X9)) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f86,f48])).
% 1.68/0.58  fof(f48,plain,(
% 1.68/0.58    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f18])).
% 1.68/0.58  fof(f18,plain,(
% 1.68/0.58    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.68/0.58    inference(ennf_transformation,[],[f11])).
% 1.68/0.58  fof(f11,axiom,(
% 1.68/0.58    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).
% 1.68/0.58  fof(f1925,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | spl7_97),
% 1.68/0.58    inference(avatar_component_clause,[],[f1923])).
% 1.68/0.58  fof(f1701,plain,(
% 1.68/0.58    ~spl7_13 | ~spl7_22 | spl7_88),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f1700])).
% 1.68/0.58  fof(f1700,plain,(
% 1.68/0.58    $false | (~spl7_13 | ~spl7_22 | spl7_88)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1699,f276])).
% 1.68/0.58  fof(f276,plain,(
% 1.68/0.58    m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl7_22),
% 1.68/0.58    inference(avatar_component_clause,[],[f275])).
% 1.68/0.58  fof(f275,plain,(
% 1.68/0.58    spl7_22 <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.68/0.58  fof(f1699,plain,(
% 1.68/0.58    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | (~spl7_13 | spl7_88)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1697,f164])).
% 1.68/0.58  fof(f164,plain,(
% 1.68/0.58    r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~spl7_13),
% 1.68/0.58    inference(avatar_component_clause,[],[f162])).
% 1.68/0.58  fof(f162,plain,(
% 1.68/0.58    spl7_13 <=> r2_hidden(sK6(sK0,sK2,sK3),sK2)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.68/0.58  fof(f1697,plain,(
% 1.68/0.58    ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl7_88),
% 1.68/0.58    inference(resolution,[],[f1691,f28])).
% 1.68/0.58  fof(f28,plain,(
% 1.68/0.58    ( ! [X4] : (r1_yellow_0(sK0,sK4(X4)) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f16,plain,(
% 1.68/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.68/0.58    inference(flattening,[],[f15])).
% 1.68/0.58  fof(f15,plain,(
% 1.68/0.58    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.68/0.58    inference(ennf_transformation,[],[f14])).
% 1.68/0.58  fof(f14,plain,(
% 1.68/0.58    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 1.68/0.58    inference(rectify,[],[f13])).
% 1.68/0.58  fof(f13,negated_conjecture,(
% 1.68/0.58    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 1.68/0.58    inference(negated_conjecture,[],[f12])).
% 1.68/0.58  fof(f12,conjecture,(
% 1.68/0.58    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).
% 1.68/0.58  fof(f1691,plain,(
% 1.68/0.58    ~r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | spl7_88),
% 1.68/0.58    inference(avatar_component_clause,[],[f1689])).
% 1.68/0.58  fof(f1555,plain,(
% 1.68/0.58    ~spl7_27 | spl7_40 | spl7_85),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f1554])).
% 1.68/0.58  fof(f1554,plain,(
% 1.68/0.58    $false | (~spl7_27 | spl7_40 | spl7_85)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1553,f43])).
% 1.68/0.58  fof(f43,plain,(
% 1.68/0.58    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f5])).
% 1.68/0.58  fof(f5,axiom,(
% 1.68/0.58    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).
% 1.68/0.58  fof(f1553,plain,(
% 1.68/0.58    ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_27 | spl7_40 | spl7_85)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1552,f602])).
% 1.68/0.58  fof(f602,plain,(
% 1.68/0.58    k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3)) | spl7_40),
% 1.68/0.58    inference(avatar_component_clause,[],[f601])).
% 1.68/0.58  fof(f601,plain,(
% 1.68/0.58    spl7_40 <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.68/0.58  fof(f1552,plain,(
% 1.68/0.58    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_27 | spl7_85)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1551,f417])).
% 1.68/0.58  fof(f417,plain,(
% 1.68/0.58    m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~spl7_27),
% 1.68/0.58    inference(avatar_component_clause,[],[f415])).
% 1.68/0.58  fof(f415,plain,(
% 1.68/0.58    spl7_27 <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.68/0.58  fof(f1551,plain,(
% 1.68/0.58    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_85),
% 1.68/0.58    inference(resolution,[],[f1528,f34])).
% 1.68/0.58  fof(f34,plain,(
% 1.68/0.58    ( ! [X6] : (r1_yellow_0(sK0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK1)) | k1_xboole_0 = X6 | ~v1_finset_1(X6)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f1528,plain,(
% 1.68/0.58    ~r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | spl7_85),
% 1.68/0.58    inference(avatar_component_clause,[],[f1526])).
% 1.68/0.58  fof(f1526,plain,(
% 1.68/0.58    spl7_85 <=> r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).
% 1.68/0.58  fof(f1529,plain,(
% 1.68/0.58    ~spl7_85 | ~spl7_4 | spl7_83),
% 1.68/0.58    inference(avatar_split_clause,[],[f1511,f1501,f84,f1526])).
% 1.68/0.58  fof(f1501,plain,(
% 1.68/0.58    spl7_83 <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).
% 1.68/0.58  fof(f1511,plain,(
% 1.68/0.58    ~r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_4 | spl7_83)),
% 1.68/0.58    inference(resolution,[],[f1503,f143])).
% 1.68/0.58  fof(f143,plain,(
% 1.68/0.58    ( ! [X2] : (r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) | ~r1_yellow_0(sK0,X2)) ) | ~spl7_4),
% 1.68/0.58    inference(subsumption_resolution,[],[f141,f86])).
% 1.68/0.58  fof(f141,plain,(
% 1.68/0.58    ( ! [X2] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X2) | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2))) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f101,f66])).
% 1.68/0.58  fof(f66,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))) )),
% 1.68/0.58    inference(equality_resolution,[],[f54])).
% 1.68/0.58  fof(f54,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2) )),
% 1.68/0.58    inference(cnf_transformation,[],[f20])).
% 1.68/0.58  fof(f1503,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | spl7_83),
% 1.68/0.58    inference(avatar_component_clause,[],[f1501])).
% 1.68/0.58  fof(f1504,plain,(
% 1.68/0.58    ~spl7_83 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_10 | spl7_28 | ~spl7_39),
% 1.68/0.58    inference(avatar_split_clause,[],[f1348,f597,f427,f129,f103,f84,f79,f1501])).
% 1.68/0.58  fof(f79,plain,(
% 1.68/0.58    spl7_3 <=> v4_orders_2(sK0)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.68/0.58  fof(f129,plain,(
% 1.68/0.58    spl7_10 <=> r2_lattice3(sK0,sK2,sK3)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.68/0.58  fof(f427,plain,(
% 1.68/0.58    spl7_28 <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.68/0.58  fof(f597,plain,(
% 1.68/0.58    spl7_39 <=> r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 1.68/0.58  fof(f1348,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_10 | spl7_28 | ~spl7_39)),
% 1.68/0.58    inference(subsumption_resolution,[],[f1347,f101])).
% 1.68/0.58  fof(f1347,plain,(
% 1.68/0.58    ~m1_subset_1(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_10 | spl7_28 | ~spl7_39)),
% 1.68/0.58    inference(resolution,[],[f1341,f599])).
% 1.68/0.58  fof(f599,plain,(
% 1.68/0.58    r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_39),
% 1.68/0.58    inference(avatar_component_clause,[],[f597])).
% 1.68/0.58  fof(f1341,plain,(
% 1.68/0.58    ( ! [X12] : (~r2_hidden(X12,sK2) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X12)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_10 | spl7_28)),
% 1.68/0.58    inference(resolution,[],[f830,f131])).
% 1.68/0.58  fof(f131,plain,(
% 1.68/0.58    r2_lattice3(sK0,sK2,sK3) | ~spl7_10),
% 1.68/0.58    inference(avatar_component_clause,[],[f129])).
% 1.68/0.58  fof(f830,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_lattice3(sK0,X1,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_28)),
% 1.68/0.58    inference(subsumption_resolution,[],[f829,f105])).
% 1.68/0.58  fof(f829,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X1,sK3)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_28)),
% 1.68/0.58    inference(duplicate_literal_removal,[],[f823])).
% 1.68/0.58  fof(f823,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X1,sK3)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_28)),
% 1.68/0.58    inference(resolution,[],[f438,f98])).
% 1.68/0.58  fof(f98,plain,(
% 1.68/0.58    ( ! [X19,X20,X18] : (r1_orders_2(sK0,X19,X18) | ~m1_subset_1(X19,u1_struct_0(sK0)) | ~r2_hidden(X19,X20) | ~m1_subset_1(X18,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X20,X18)) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f86,f55])).
% 1.68/0.58  fof(f55,plain,(
% 1.68/0.58    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f22])).
% 1.68/0.58  fof(f22,plain,(
% 1.68/0.58    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.68/0.58    inference(flattening,[],[f21])).
% 1.68/0.58  fof(f21,plain,(
% 1.68/0.58    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.68/0.58    inference(ennf_transformation,[],[f6])).
% 1.68/0.58  fof(f6,axiom,(
% 1.68/0.58    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 1.68/0.58  fof(f438,plain,(
% 1.68/0.58    ( ! [X0] : (~r1_orders_2(sK0,X0,sK3) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_28)),
% 1.68/0.58    inference(subsumption_resolution,[],[f433,f105])).
% 1.68/0.58  fof(f433,plain,(
% 1.68/0.58    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK3) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_3 | ~spl7_4 | spl7_28)),
% 1.68/0.58    inference(resolution,[],[f429,f188])).
% 1.68/0.58  fof(f188,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (r2_lattice3(sK0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r2_lattice3(sK0,X2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_3 | ~spl7_4)),
% 1.68/0.58    inference(subsumption_resolution,[],[f88,f86])).
% 1.68/0.58  fof(f88,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r2_lattice3(sK0,X2,X0) | r2_lattice3(sK0,X2,X1)) ) | ~spl7_3),
% 1.68/0.58    inference(resolution,[],[f81,f59])).
% 1.68/0.58  fof(f59,plain,(
% 1.68/0.58    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r2_lattice3(X0,X3,X1) | r2_lattice3(X0,X3,X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f24])).
% 1.68/0.58  fof(f24,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 1.68/0.58    inference(flattening,[],[f23])).
% 1.68/0.58  fof(f23,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 1.68/0.58    inference(ennf_transformation,[],[f9])).
% 1.68/0.58  fof(f9,axiom,(
% 1.68/0.58    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).
% 1.68/0.58  fof(f81,plain,(
% 1.68/0.58    v4_orders_2(sK0) | ~spl7_3),
% 1.68/0.58    inference(avatar_component_clause,[],[f79])).
% 1.68/0.58  fof(f429,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | spl7_28),
% 1.68/0.58    inference(avatar_component_clause,[],[f427])).
% 1.68/0.58  fof(f671,plain,(
% 1.68/0.58    ~spl7_40),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f670])).
% 1.68/0.58  fof(f670,plain,(
% 1.68/0.58    $false | ~spl7_40),
% 1.68/0.58    inference(subsumption_resolution,[],[f660,f41])).
% 1.68/0.58  fof(f41,plain,(
% 1.68/0.58    v1_xboole_0(k1_xboole_0)),
% 1.68/0.58    inference(cnf_transformation,[],[f1])).
% 1.68/0.58  fof(f1,axiom,(
% 1.68/0.58    v1_xboole_0(k1_xboole_0)),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.68/0.58  fof(f660,plain,(
% 1.68/0.58    ~v1_xboole_0(k1_xboole_0) | ~spl7_40),
% 1.68/0.58    inference(superposition,[],[f42,f603])).
% 1.68/0.58  fof(f603,plain,(
% 1.68/0.58    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~spl7_40),
% 1.68/0.58    inference(avatar_component_clause,[],[f601])).
% 1.68/0.58  fof(f42,plain,(
% 1.68/0.58    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f2])).
% 1.68/0.58  fof(f2,axiom,(
% 1.68/0.58    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.68/0.58  fof(f604,plain,(
% 1.68/0.58    spl7_39 | spl7_40 | ~spl7_27),
% 1.68/0.58    inference(avatar_split_clause,[],[f425,f415,f601,f597])).
% 1.68/0.58  fof(f425,plain,(
% 1.68/0.58    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_27),
% 1.68/0.58    inference(subsumption_resolution,[],[f422,f43])).
% 1.68/0.58  fof(f422,plain,(
% 1.68/0.58    ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_27),
% 1.68/0.58    inference(resolution,[],[f417,f33])).
% 1.68/0.58  fof(f33,plain,(
% 1.68/0.58    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | ~v1_finset_1(X3) | k1_xboole_0 = X3 | r2_hidden(k1_yellow_0(sK0,X3),sK2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f430,plain,(
% 1.68/0.58    ~spl7_28 | ~spl7_4 | ~spl7_5 | spl7_9),
% 1.68/0.58    inference(avatar_split_clause,[],[f371,f125,f103,f84,f427])).
% 1.68/0.58  fof(f371,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | (~spl7_4 | ~spl7_5 | spl7_9)),
% 1.68/0.58    inference(subsumption_resolution,[],[f367,f105])).
% 1.68/0.58  fof(f367,plain,(
% 1.68/0.58    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) | (~spl7_4 | spl7_9)),
% 1.68/0.58    inference(resolution,[],[f126,f255])).
% 1.68/0.58  fof(f255,plain,(
% 1.68/0.58    ( ! [X0,X1] : (r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)) ) | ~spl7_4),
% 1.68/0.58    inference(subsumption_resolution,[],[f254,f86])).
% 1.68/0.58  fof(f254,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1) | ~l1_orders_2(sK0)) ) | ~spl7_4),
% 1.68/0.58    inference(duplicate_literal_removal,[],[f253])).
% 1.68/0.58  fof(f253,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X0,X1)) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f175,f56])).
% 1.68/0.58  fof(f56,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f22])).
% 1.68/0.58  fof(f175,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl7_4),
% 1.68/0.58    inference(duplicate_literal_removal,[],[f174])).
% 1.68/0.58  fof(f174,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f91,f100])).
% 1.68/0.58  fof(f100,plain,(
% 1.68/0.58    ( ! [X24,X23] : (~r1_orders_2(sK0,sK6(sK0,X24,X23),X23) | ~m1_subset_1(X23,u1_struct_0(sK0)) | r2_lattice3(sK0,X24,X23)) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f86,f58])).
% 1.68/0.58  fof(f58,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,sK6(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f22])).
% 1.68/0.58  fof(f91,plain,(
% 1.68/0.58    ( ! [X2,X3] : (r1_orders_2(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(X3),X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f86,f45])).
% 1.68/0.58  fof(f45,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,k1_tarski(X2),X1) | r1_orders_2(X0,X2,X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f17])).
% 1.68/0.58  fof(f17,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.68/0.58    inference(ennf_transformation,[],[f10])).
% 1.68/0.58  fof(f10,axiom,(
% 1.68/0.58    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).
% 1.68/0.58  fof(f126,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,sK1,sK3) | spl7_9),
% 1.68/0.58    inference(avatar_component_clause,[],[f125])).
% 1.68/0.58  fof(f418,plain,(
% 1.68/0.58    spl7_27 | ~spl7_18),
% 1.68/0.58    inference(avatar_split_clause,[],[f393,f219,f415])).
% 1.68/0.58  fof(f219,plain,(
% 1.68/0.58    spl7_18 <=> r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.68/0.58  fof(f393,plain,(
% 1.68/0.58    m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~spl7_18),
% 1.68/0.58    inference(resolution,[],[f221,f64])).
% 1.68/0.58  fof(f64,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f4])).
% 1.68/0.58  fof(f4,axiom,(
% 1.68/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.68/0.58  fof(f221,plain,(
% 1.68/0.58    r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) | ~spl7_18),
% 1.68/0.58    inference(avatar_component_clause,[],[f219])).
% 1.68/0.58  fof(f366,plain,(
% 1.68/0.58    spl7_26 | ~spl7_13 | ~spl7_22),
% 1.68/0.58    inference(avatar_split_clause,[],[f361,f275,f162,f363])).
% 1.68/0.58  fof(f361,plain,(
% 1.68/0.58    sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | (~spl7_13 | ~spl7_22)),
% 1.68/0.58    inference(subsumption_resolution,[],[f166,f276])).
% 1.68/0.58  fof(f166,plain,(
% 1.68/0.58    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_13),
% 1.68/0.58    inference(resolution,[],[f164,f29])).
% 1.68/0.58  fof(f29,plain,(
% 1.68/0.58    ( ! [X4] : (~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k1_yellow_0(sK0,sK4(X4)) = X4) )),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f351,plain,(
% 1.68/0.58    ~spl7_25 | ~spl7_4 | ~spl7_5 | ~spl7_22 | spl7_24),
% 1.68/0.58    inference(avatar_split_clause,[],[f340,f326,f275,f103,f84,f348])).
% 1.68/0.58  fof(f326,plain,(
% 1.68/0.58    spl7_24 <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK2,sK3)),sK3)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.68/0.58  fof(f340,plain,(
% 1.68/0.58    ~r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) | (~spl7_4 | ~spl7_5 | ~spl7_22 | spl7_24)),
% 1.68/0.58    inference(subsumption_resolution,[],[f339,f105])).
% 1.68/0.58  fof(f339,plain,(
% 1.68/0.58    ~r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_4 | ~spl7_22 | spl7_24)),
% 1.68/0.58    inference(subsumption_resolution,[],[f334,f276])).
% 1.68/0.58  fof(f334,plain,(
% 1.68/0.58    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK6(sK0,sK2,sK3),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_4 | spl7_24)),
% 1.68/0.58    inference(resolution,[],[f328,f90])).
% 1.68/0.58  fof(f90,plain,(
% 1.68/0.58    ( ! [X0,X1] : (r2_lattice3(sK0,k1_tarski(X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f86,f44])).
% 1.68/0.58  fof(f44,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | r2_lattice3(X0,k1_tarski(X2),X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f17])).
% 1.68/0.58  fof(f328,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK2,sK3)),sK3) | spl7_24),
% 1.68/0.58    inference(avatar_component_clause,[],[f326])).
% 1.68/0.58  fof(f329,plain,(
% 1.68/0.58    ~spl7_24 | ~spl7_4 | ~spl7_5 | spl7_10),
% 1.68/0.58    inference(avatar_split_clause,[],[f322,f129,f103,f84,f326])).
% 1.68/0.58  fof(f322,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK2,sK3)),sK3) | (~spl7_4 | ~spl7_5 | spl7_10)),
% 1.68/0.58    inference(subsumption_resolution,[],[f319,f105])).
% 1.68/0.58  fof(f319,plain,(
% 1.68/0.58    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK2,sK3)),sK3) | (~spl7_4 | spl7_10)),
% 1.68/0.58    inference(resolution,[],[f255,f130])).
% 1.68/0.58  fof(f130,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,sK2,sK3) | spl7_10),
% 1.68/0.58    inference(avatar_component_clause,[],[f129])).
% 1.68/0.58  fof(f300,plain,(
% 1.68/0.58    spl7_23 | ~spl7_21),
% 1.68/0.58    inference(avatar_split_clause,[],[f295,f271,f297])).
% 1.68/0.58  fof(f271,plain,(
% 1.68/0.58    spl7_21 <=> m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.68/0.58  fof(f295,plain,(
% 1.68/0.58    r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) | ~spl7_21),
% 1.68/0.58    inference(resolution,[],[f273,f65])).
% 1.68/0.58  fof(f65,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f4])).
% 1.68/0.58  fof(f273,plain,(
% 1.68/0.58    m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | ~spl7_21),
% 1.68/0.58    inference(avatar_component_clause,[],[f271])).
% 1.68/0.58  fof(f283,plain,(
% 1.68/0.58    ~spl7_4 | ~spl7_5 | spl7_10 | spl7_22),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f282])).
% 1.68/0.58  fof(f282,plain,(
% 1.68/0.58    $false | (~spl7_4 | ~spl7_5 | spl7_10 | spl7_22)),
% 1.68/0.58    inference(subsumption_resolution,[],[f281,f130])).
% 1.68/0.58  fof(f281,plain,(
% 1.68/0.58    r2_lattice3(sK0,sK2,sK3) | (~spl7_4 | ~spl7_5 | spl7_22)),
% 1.68/0.58    inference(subsumption_resolution,[],[f280,f86])).
% 1.68/0.58  fof(f280,plain,(
% 1.68/0.58    ~l1_orders_2(sK0) | r2_lattice3(sK0,sK2,sK3) | (~spl7_5 | spl7_22)),
% 1.68/0.58    inference(subsumption_resolution,[],[f279,f105])).
% 1.68/0.58  fof(f279,plain,(
% 1.68/0.58    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,sK2,sK3) | spl7_22),
% 1.68/0.58    inference(resolution,[],[f277,f56])).
% 1.68/0.58  fof(f277,plain,(
% 1.68/0.58    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl7_22),
% 1.68/0.58    inference(avatar_component_clause,[],[f275])).
% 1.68/0.58  fof(f278,plain,(
% 1.68/0.58    spl7_21 | ~spl7_22 | ~spl7_13),
% 1.68/0.58    inference(avatar_split_clause,[],[f167,f162,f275,f271])).
% 1.68/0.58  fof(f167,plain,(
% 1.68/0.58    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | ~spl7_13),
% 1.68/0.58    inference(resolution,[],[f164,f27])).
% 1.68/0.58  fof(f27,plain,(
% 1.68/0.58    ( ! [X4] : (~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0)) | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f222,plain,(
% 1.68/0.58    spl7_18 | ~spl7_12),
% 1.68/0.58    inference(avatar_split_clause,[],[f217,f149,f219])).
% 1.68/0.58  fof(f149,plain,(
% 1.68/0.58    spl7_12 <=> r2_hidden(sK6(sK0,sK1,sK3),sK1)),
% 1.68/0.58    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.68/0.58  fof(f217,plain,(
% 1.68/0.58    r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) | ~spl7_12),
% 1.68/0.58    inference(resolution,[],[f151,f62])).
% 1.68/0.58  fof(f62,plain,(
% 1.68/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f3])).
% 1.68/0.58  fof(f3,axiom,(
% 1.68/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.68/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.68/0.58  fof(f151,plain,(
% 1.68/0.58    r2_hidden(sK6(sK0,sK1,sK3),sK1) | ~spl7_12),
% 1.68/0.58    inference(avatar_component_clause,[],[f149])).
% 1.68/0.58  fof(f165,plain,(
% 1.68/0.58    spl7_13 | ~spl7_4 | ~spl7_5 | spl7_10),
% 1.68/0.58    inference(avatar_split_clause,[],[f160,f129,f103,f84,f162])).
% 1.68/0.58  fof(f160,plain,(
% 1.68/0.58    r2_hidden(sK6(sK0,sK2,sK3),sK2) | (~spl7_4 | ~spl7_5 | spl7_10)),
% 1.68/0.58    inference(subsumption_resolution,[],[f158,f105])).
% 1.68/0.58  fof(f158,plain,(
% 1.68/0.58    r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_4 | spl7_10)),
% 1.68/0.58    inference(resolution,[],[f130,f99])).
% 1.68/0.58  fof(f99,plain,(
% 1.68/0.58    ( ! [X21,X22] : (r2_lattice3(sK0,X22,X21) | r2_hidden(sK6(sK0,X22,X21),X22) | ~m1_subset_1(X21,u1_struct_0(sK0))) ) | ~spl7_4),
% 1.68/0.58    inference(resolution,[],[f86,f57])).
% 1.68/0.58  fof(f57,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK6(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 1.68/0.58    inference(cnf_transformation,[],[f22])).
% 1.68/0.58  fof(f155,plain,(
% 1.68/0.58    ~spl7_9 | ~spl7_10),
% 1.68/0.58    inference(avatar_contradiction_clause,[],[f154])).
% 1.68/0.58  fof(f154,plain,(
% 1.68/0.58    $false | (~spl7_9 | ~spl7_10)),
% 1.68/0.58    inference(subsumption_resolution,[],[f153,f127])).
% 1.68/0.58  fof(f153,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,sK1,sK3) | ~spl7_10),
% 1.68/0.58    inference(subsumption_resolution,[],[f31,f131])).
% 1.68/0.58  fof(f31,plain,(
% 1.68/0.58    ~r2_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK1,sK3)),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f152,plain,(
% 1.68/0.58    spl7_12 | ~spl7_4 | ~spl7_5 | spl7_9),
% 1.68/0.58    inference(avatar_split_clause,[],[f145,f125,f103,f84,f149])).
% 1.68/0.58  fof(f145,plain,(
% 1.68/0.58    r2_hidden(sK6(sK0,sK1,sK3),sK1) | (~spl7_4 | ~spl7_5 | spl7_9)),
% 1.68/0.58    inference(subsumption_resolution,[],[f144,f105])).
% 1.68/0.58  fof(f144,plain,(
% 1.68/0.58    r2_hidden(sK6(sK0,sK1,sK3),sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_4 | spl7_9)),
% 1.68/0.58    inference(resolution,[],[f99,f126])).
% 1.68/0.58  fof(f132,plain,(
% 1.68/0.58    spl7_9 | spl7_10),
% 1.68/0.58    inference(avatar_split_clause,[],[f30,f129,f125])).
% 1.68/0.58  fof(f30,plain,(
% 1.68/0.58    r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3)),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f106,plain,(
% 1.68/0.58    spl7_5),
% 1.68/0.58    inference(avatar_split_clause,[],[f32,f103])).
% 1.68/0.58  fof(f32,plain,(
% 1.68/0.58    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f87,plain,(
% 1.68/0.58    spl7_4),
% 1.68/0.58    inference(avatar_split_clause,[],[f40,f84])).
% 1.68/0.58  fof(f40,plain,(
% 1.68/0.58    l1_orders_2(sK0)),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  fof(f82,plain,(
% 1.68/0.58    spl7_3),
% 1.68/0.58    inference(avatar_split_clause,[],[f39,f79])).
% 1.68/0.58  fof(f39,plain,(
% 1.68/0.58    v4_orders_2(sK0)),
% 1.68/0.58    inference(cnf_transformation,[],[f16])).
% 1.68/0.58  % SZS output end Proof for theBenchmark
% 1.68/0.58  % (28047)------------------------------
% 1.68/0.58  % (28047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (28047)Termination reason: Refutation
% 1.68/0.58  
% 1.68/0.58  % (28047)Memory used [KB]: 11513
% 1.68/0.58  % (28047)Time elapsed: 0.139 s
% 1.68/0.58  % (28047)------------------------------
% 1.68/0.58  % (28047)------------------------------
% 1.68/0.58  % (28043)Success in time 0.218 s
%------------------------------------------------------------------------------
