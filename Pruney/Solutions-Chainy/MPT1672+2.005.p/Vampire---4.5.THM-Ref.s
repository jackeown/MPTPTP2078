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

% Result     : Theorem 1.94s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 460 expanded)
%              Number of leaves         :   38 ( 161 expanded)
%              Depth                    :   21
%              Number of atoms          :  937 (2913 expanded)
%              Number of equality atoms :   59 ( 273 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1630,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f87,f106,f111,f116,f134,f151,f154,f164,f184,f236,f268,f299,f316,f331,f357,f607,f635,f1155,f1345,f1379,f1388,f1435,f1448,f1489,f1583,f1629])).

fof(f1629,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_24
    | spl7_132 ),
    inference(avatar_contradiction_clause,[],[f1628])).

fof(f1628,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_24
    | spl7_132 ),
    inference(subsumption_resolution,[],[f1627,f129])).

fof(f129,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_9
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1627,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_24
    | spl7_132 ),
    inference(resolution,[],[f1588,f330])).

fof(f330,plain,
    ( r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl7_24
  <=> r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f1588,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r2_lattice3(sK0,X0,sK3) )
    | ~ spl7_4
    | ~ spl7_5
    | spl7_132 ),
    inference(subsumption_resolution,[],[f1585,f105])).

fof(f105,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1585,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,sK3)
        | ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0) )
    | ~ spl7_4
    | spl7_132 ),
    inference(resolution,[],[f1582,f92])).

fof(f92,plain,
    ( ! [X10,X8,X9] :
        ( r2_lattice3(sK0,X8,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X9,X10)
        | ~ r1_tarski(X8,X9) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f86,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1582,plain,
    ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | spl7_132 ),
    inference(avatar_component_clause,[],[f1580])).

fof(f1580,plain,
    ( spl7_132
  <=> r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f1583,plain,
    ( ~ spl7_132
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10
    | ~ spl7_15
    | ~ spl7_21
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f1533,f476,f265,f181,f131,f103,f84,f1580])).

fof(f131,plain,
    ( spl7_10
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f181,plain,
    ( spl7_15
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f265,plain,
    ( spl7_21
  <=> sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f476,plain,
    ( spl7_39
  <=> r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f1533,plain,
    ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10
    | ~ spl7_15
    | ~ spl7_21
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f1532,f132])).

fof(f132,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1532,plain,
    ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15
    | ~ spl7_21
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f1531,f105])).

fof(f1531,plain,
    ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_15
    | ~ spl7_21
    | ~ spl7_39 ),
    inference(duplicate_literal_removal,[],[f1526])).

fof(f1526,plain,
    ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_15
    | ~ spl7_21
    | ~ spl7_39 ),
    inference(resolution,[],[f1520,f98])).

fof(f98,plain,
    ( ! [X24,X23] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X24,X23),X23)
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | r2_lattice3(sK0,X24,X23) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f1520,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0)
        | ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_15
    | ~ spl7_21
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f324,f477])).

fof(f477,plain,
    ( r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f476])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0) )
    | ~ spl7_4
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f323,f86])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0) )
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f321,f183])).

fof(f183,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0) )
    | ~ spl7_21 ),
    inference(superposition,[],[f67,f267])).

fof(f267,plain,
    ( sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f265])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f1489,plain,
    ( ~ spl7_13
    | ~ spl7_15
    | spl7_39 ),
    inference(avatar_contradiction_clause,[],[f1488])).

fof(f1488,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_15
    | spl7_39 ),
    inference(subsumption_resolution,[],[f1453,f163])).

fof(f163,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_13
  <=> r2_hidden(sK6(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f1453,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_15
    | spl7_39 ),
    inference(subsumption_resolution,[],[f480,f183])).

fof(f480,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_39 ),
    inference(resolution,[],[f478,f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).

fof(f478,plain,
    ( ~ r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | spl7_39 ),
    inference(avatar_component_clause,[],[f476])).

fof(f1448,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_22
    | ~ spl7_127 ),
    inference(avatar_contradiction_clause,[],[f1447])).

fof(f1447,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_22
    | ~ spl7_127 ),
    inference(subsumption_resolution,[],[f1446,f128])).

fof(f128,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1446,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_10
    | ~ spl7_22
    | ~ spl7_127 ),
    inference(subsumption_resolution,[],[f1445,f133])).

fof(f133,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1445,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_22
    | ~ spl7_127 ),
    inference(subsumption_resolution,[],[f1444,f105])).

fof(f1444,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | ~ spl7_22
    | ~ spl7_127 ),
    inference(subsumption_resolution,[],[f1437,f298])).

fof(f298,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl7_22
  <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f1437,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | ~ spl7_127 ),
    inference(resolution,[],[f1434,f186])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK6(sK0,X0,X1),X2)
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X2,X1)
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_hidden(sK6(sK0,X0,X1),X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f96,f98])).

fof(f96,plain,
    ( ! [X19,X20,X18] :
        ( r1_orders_2(sK0,X19,X18)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ r2_hidden(X19,X20)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X20,X18) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1434,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK2)
    | ~ spl7_127 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1432,plain,
    ( spl7_127
  <=> r2_hidden(sK6(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_127])])).

fof(f1435,plain,
    ( spl7_127
    | ~ spl7_50
    | ~ spl7_122 ),
    inference(avatar_split_clause,[],[f1413,f1342,f600,f1432])).

fof(f600,plain,
    ( spl7_50
  <=> r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f1342,plain,
    ( spl7_122
  <=> sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f1413,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK2)
    | ~ spl7_50
    | ~ spl7_122 ),
    inference(superposition,[],[f602,f1344])).

fof(f1344,plain,
    ( sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_122 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f602,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f600])).

fof(f1388,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_22
    | spl7_125 ),
    inference(avatar_contradiction_clause,[],[f1387])).

fof(f1387,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_22
    | spl7_125 ),
    inference(subsumption_resolution,[],[f1380,f298])).

fof(f1380,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_125 ),
    inference(resolution,[],[f1378,f101])).

fof(f101,plain,
    ( ! [X25] :
        ( r1_orders_2(sK0,X25,X25)
        | ~ m1_subset_1(X25,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f100,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f100,plain,
    ( ! [X25] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X25,u1_struct_0(sK0))
        | r1_orders_2(sK0,X25,X25) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f99,f76])).

fof(f76,plain,
    ( v3_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f99,plain,
    ( ! [X25] :
        ( ~ v3_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X25,u1_struct_0(sK0))
        | r1_orders_2(sK0,X25,X25) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f1378,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3))
    | spl7_125 ),
    inference(avatar_component_clause,[],[f1376])).

fof(f1376,plain,
    ( spl7_125
  <=> r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).

fof(f1379,plain,
    ( ~ spl7_125
    | ~ spl7_4
    | ~ spl7_22
    | spl7_121 ),
    inference(avatar_split_clause,[],[f1353,f1338,f296,f84,f1376])).

fof(f1338,plain,
    ( spl7_121
  <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).

fof(f1353,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3))
    | ~ spl7_4
    | ~ spl7_22
    | spl7_121 ),
    inference(subsumption_resolution,[],[f1352,f298])).

fof(f1352,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3))
    | ~ spl7_4
    | spl7_121 ),
    inference(duplicate_literal_removal,[],[f1347])).

fof(f1347,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_121 ),
    inference(resolution,[],[f1340,f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,k1_tarski(X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | r2_lattice3(X0,k1_tarski(X2),X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f1340,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | spl7_121 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f1345,plain,
    ( ~ spl7_121
    | spl7_122
    | ~ spl7_4
    | ~ spl7_22
    | ~ spl7_26
    | spl7_51
    | ~ spl7_102 ),
    inference(avatar_split_clause,[],[f1336,f1147,f604,f354,f296,f84,f1342,f1338])).

fof(f354,plain,
    ( spl7_26
  <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f604,plain,
    ( spl7_51
  <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f1147,plain,
    ( spl7_102
  <=> r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f1336,plain,
    ( sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | ~ spl7_4
    | ~ spl7_22
    | ~ spl7_26
    | spl7_51
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1335,f1148])).

fof(f1148,plain,
    ( r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f1335,plain,
    ( sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_4
    | ~ spl7_22
    | ~ spl7_26
    | spl7_51
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1333,f298])).

fof(f1333,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_4
    | ~ spl7_26
    | spl7_51
    | ~ spl7_102 ),
    inference(duplicate_literal_removal,[],[f1329])).

fof(f1329,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_4
    | ~ spl7_26
    | spl7_51
    | ~ spl7_102 ),
    inference(resolution,[],[f1326,f94])).

fof(f94,plain,
    ( ! [X14,X15] :
        ( r2_lattice3(sK0,X15,sK5(sK0,X15,X14))
        | ~ r1_yellow_0(sK0,X15)
        | ~ r2_lattice3(sK0,X15,X14)
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | k1_yellow_0(sK0,X15) = X14 )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1326,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,k1_tarski(X0),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) )
    | ~ spl7_4
    | ~ spl7_26
    | spl7_51
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f1094,f1148])).

fof(f1094,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(X0),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) )
    | ~ spl7_4
    | ~ spl7_26
    | spl7_51 ),
    inference(subsumption_resolution,[],[f1093,f86])).

fof(f1093,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(X0),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4
    | ~ spl7_26
    | spl7_51 ),
    inference(duplicate_literal_removal,[],[f1092])).

fof(f1092,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(X0),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ l1_orders_2(sK0)
        | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0 )
    | ~ spl7_4
    | ~ spl7_26
    | spl7_51 ),
    inference(resolution,[],[f821,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f821,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3),u1_struct_0(sK0))
        | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(X3),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3) )
    | ~ spl7_4
    | ~ spl7_26
    | spl7_51 ),
    inference(duplicate_literal_removal,[],[f820])).

fof(f820,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3)
        | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(X3),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3))
        | ~ m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3),u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_26
    | spl7_51 ),
    inference(resolution,[],[f812,f89])).

fof(f89,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(X3),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f812,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_26
    | spl7_51 ),
    inference(subsumption_resolution,[],[f364,f605])).

fof(f605,plain,
    ( k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3))
    | spl7_51 ),
    inference(avatar_component_clause,[],[f604])).

fof(f364,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ r1_orders_2(sK0,X0,sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0))
        | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) )
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f360,f44])).

fof(f44,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f360,plain,
    ( ! [X0] :
        ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)
        | ~ r1_orders_2(sK0,X0,sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0))
        | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
        | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) )
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(resolution,[],[f356,f188])).

fof(f188,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | ~ r2_lattice3(sK0,X3,X2)
        | ~ r1_orders_2(sK0,X2,sK5(sK0,X3,X2))
        | k1_yellow_0(sK0,X3) = X2
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k1_xboole_0 = X3
        | ~ v1_finset_1(X3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f95,f35])).

fof(f35,plain,(
    ! [X6] :
      ( r1_yellow_0(sK0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X6
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,
    ( ! [X17,X16] :
        ( ~ r1_yellow_0(sK0,X17)
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X17,X16)
        | ~ r1_orders_2(sK0,X16,sK5(sK0,X17,X16))
        | k1_yellow_0(sK0,X17) = X16 )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f356,plain,
    ( m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f354])).

fof(f1155,plain,
    ( ~ spl7_26
    | spl7_51
    | spl7_102 ),
    inference(avatar_contradiction_clause,[],[f1154])).

fof(f1154,plain,
    ( $false
    | ~ spl7_26
    | spl7_51
    | spl7_102 ),
    inference(subsumption_resolution,[],[f1153,f44])).

fof(f1153,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_26
    | spl7_51
    | spl7_102 ),
    inference(subsumption_resolution,[],[f1152,f605])).

fof(f1152,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_26
    | spl7_102 ),
    inference(subsumption_resolution,[],[f1151,f356])).

fof(f1151,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_102 ),
    inference(resolution,[],[f1149,f35])).

fof(f1149,plain,
    ( ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_102 ),
    inference(avatar_component_clause,[],[f1147])).

fof(f635,plain,(
    ~ spl7_51 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | ~ spl7_51 ),
    inference(subsumption_resolution,[],[f627,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f627,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_51 ),
    inference(superposition,[],[f43,f606])).

fof(f606,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f604])).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f607,plain,
    ( spl7_50
    | spl7_51
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f365,f354,f604,f600])).

fof(f365,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f361,f44])).

fof(f361,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_26 ),
    inference(resolution,[],[f356,f34])).

fof(f34,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | k1_xboole_0 = X3
      | r2_hidden(k1_yellow_0(sK0,X3),sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f357,plain,
    ( spl7_26
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f282,f233,f354])).

fof(f233,plain,
    ( spl7_19
  <=> r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f282,plain,
    ( m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_19 ),
    inference(resolution,[],[f235,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f235,plain,
    ( r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f233])).

fof(f331,plain,
    ( spl7_24
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f320,f313,f328])).

fof(f313,plain,
    ( spl7_23
  <=> m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f320,plain,
    ( r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)
    | ~ spl7_23 ),
    inference(resolution,[],[f315,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f315,plain,
    ( m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f313])).

fof(f316,plain,
    ( spl7_23
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f292,f181,f161,f313])).

fof(f292,plain,
    ( m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f289,f183])).

fof(f289,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_13 ),
    inference(resolution,[],[f163,f28])).

fof(f28,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f299,plain,
    ( spl7_22
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f276,f148,f113,f296])).

fof(f113,plain,
    ( spl7_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f148,plain,
    ( spl7_12
  <=> r2_hidden(sK6(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f276,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(resolution,[],[f150,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f115,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f115,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f150,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f268,plain,
    ( spl7_21
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f165,f161,f108,f265])).

fof(f108,plain,
    ( spl7_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f165,plain,
    ( sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(resolution,[],[f163,f142])).

fof(f142,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | k1_yellow_0(sK0,sK4(X4)) = X4 )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f30,f117])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f110,f65])).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f30,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | k1_yellow_0(sK0,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f236,plain,
    ( spl7_19
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f231,f148,f233])).

fof(f231,plain,
    ( r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f150,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f184,plain,
    ( spl7_15
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f166,f161,f108,f181])).

fof(f166,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(resolution,[],[f163,f117])).

fof(f164,plain,
    ( spl7_13
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10 ),
    inference(avatar_split_clause,[],[f159,f131,f103,f84,f161])).

fof(f159,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10 ),
    inference(subsumption_resolution,[],[f157,f105])).

fof(f157,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_10 ),
    inference(resolution,[],[f132,f97])).

fof(f97,plain,
    ( ! [X21,X22] :
        ( r2_lattice3(sK0,X22,X21)
        | r2_hidden(sK6(sK0,X22,X21),X22)
        | ~ m1_subset_1(X21,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f154,plain,
    ( ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f152,f129])).

fof(f152,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f32,f133])).

fof(f32,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f151,plain,
    ( spl7_12
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(avatar_split_clause,[],[f144,f127,f103,f84,f148])).

fof(f144,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(subsumption_resolution,[],[f143,f105])).

fof(f143,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_9 ),
    inference(resolution,[],[f97,f128])).

fof(f134,plain,
    ( spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f31,f131,f127])).

fof(f31,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f116,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f37,f113])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f36,f108])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f33,f103])).

fof(f33,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:39:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (9691)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (9702)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (9694)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (9705)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (9699)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (9697)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (9689)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (9692)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  % (9698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (9693)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (9704)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.53  % (9686)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (9690)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (9687)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (9696)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.53  % (9703)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % (9695)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.54  % (9688)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (9700)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.54  % (9701)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.54  % (9706)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.94/0.62  % (9689)Refutation found. Thanks to Tanya!
% 1.94/0.62  % SZS status Theorem for theBenchmark
% 2.07/0.63  % SZS output start Proof for theBenchmark
% 2.07/0.63  fof(f1630,plain,(
% 2.07/0.63    $false),
% 2.07/0.63    inference(avatar_sat_refutation,[],[f72,f77,f87,f106,f111,f116,f134,f151,f154,f164,f184,f236,f268,f299,f316,f331,f357,f607,f635,f1155,f1345,f1379,f1388,f1435,f1448,f1489,f1583,f1629])).
% 2.07/0.63  fof(f1629,plain,(
% 2.07/0.63    ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_24 | spl7_132),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f1628])).
% 2.07/0.63  fof(f1628,plain,(
% 2.07/0.63    $false | (~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_24 | spl7_132)),
% 2.07/0.63    inference(subsumption_resolution,[],[f1627,f129])).
% 2.07/0.63  fof(f129,plain,(
% 2.07/0.63    r2_lattice3(sK0,sK1,sK3) | ~spl7_9),
% 2.07/0.63    inference(avatar_component_clause,[],[f127])).
% 2.07/0.63  fof(f127,plain,(
% 2.07/0.63    spl7_9 <=> r2_lattice3(sK0,sK1,sK3)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.07/0.63  fof(f1627,plain,(
% 2.07/0.63    ~r2_lattice3(sK0,sK1,sK3) | (~spl7_4 | ~spl7_5 | ~spl7_24 | spl7_132)),
% 2.07/0.63    inference(resolution,[],[f1588,f330])).
% 2.07/0.63  fof(f330,plain,(
% 2.07/0.63    r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) | ~spl7_24),
% 2.07/0.63    inference(avatar_component_clause,[],[f328])).
% 2.07/0.63  fof(f328,plain,(
% 2.07/0.63    spl7_24 <=> r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.07/0.63  fof(f1588,plain,(
% 2.07/0.63    ( ! [X0] : (~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0) | ~r2_lattice3(sK0,X0,sK3)) ) | (~spl7_4 | ~spl7_5 | spl7_132)),
% 2.07/0.63    inference(subsumption_resolution,[],[f1585,f105])).
% 2.07/0.63  fof(f105,plain,(
% 2.07/0.63    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl7_5),
% 2.07/0.63    inference(avatar_component_clause,[],[f103])).
% 2.07/0.63  fof(f103,plain,(
% 2.07/0.63    spl7_5 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.07/0.63  fof(f1585,plain,(
% 2.07/0.63    ( ! [X0] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X0,sK3) | ~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X0)) ) | (~spl7_4 | spl7_132)),
% 2.07/0.63    inference(resolution,[],[f1582,f92])).
% 2.07/0.63  fof(f92,plain,(
% 2.07/0.63    ( ! [X10,X8,X9] : (r2_lattice3(sK0,X8,X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X9,X10) | ~r1_tarski(X8,X9)) ) | ~spl7_4),
% 2.07/0.63    inference(resolution,[],[f86,f49])).
% 2.07/0.63  fof(f49,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X3) | r2_lattice3(X0,X1,X3)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f18])).
% 2.07/0.63  fof(f18,plain,(
% 2.07/0.63    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 2.07/0.63    inference(ennf_transformation,[],[f11])).
% 2.07/0.63  fof(f11,axiom,(
% 2.07/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 2.07/0.63  fof(f86,plain,(
% 2.07/0.63    l1_orders_2(sK0) | ~spl7_4),
% 2.07/0.63    inference(avatar_component_clause,[],[f84])).
% 2.07/0.63  fof(f84,plain,(
% 2.07/0.63    spl7_4 <=> l1_orders_2(sK0)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.07/0.63  fof(f1582,plain,(
% 2.07/0.63    ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | spl7_132),
% 2.07/0.63    inference(avatar_component_clause,[],[f1580])).
% 2.07/0.63  fof(f1580,plain,(
% 2.07/0.63    spl7_132 <=> r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).
% 2.07/0.63  fof(f1583,plain,(
% 2.07/0.63    ~spl7_132 | ~spl7_4 | ~spl7_5 | spl7_10 | ~spl7_15 | ~spl7_21 | ~spl7_39),
% 2.07/0.63    inference(avatar_split_clause,[],[f1533,f476,f265,f181,f131,f103,f84,f1580])).
% 2.07/0.63  fof(f131,plain,(
% 2.07/0.63    spl7_10 <=> r2_lattice3(sK0,sK2,sK3)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.07/0.63  fof(f181,plain,(
% 2.07/0.63    spl7_15 <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.07/0.63  fof(f265,plain,(
% 2.07/0.63    spl7_21 <=> sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 2.07/0.63  fof(f476,plain,(
% 2.07/0.63    spl7_39 <=> r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 2.07/0.63  fof(f1533,plain,(
% 2.07/0.63    ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | (~spl7_4 | ~spl7_5 | spl7_10 | ~spl7_15 | ~spl7_21 | ~spl7_39)),
% 2.07/0.63    inference(subsumption_resolution,[],[f1532,f132])).
% 2.07/0.63  fof(f132,plain,(
% 2.07/0.63    ~r2_lattice3(sK0,sK2,sK3) | spl7_10),
% 2.07/0.63    inference(avatar_component_clause,[],[f131])).
% 2.07/0.63  fof(f1532,plain,(
% 2.07/0.63    ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | r2_lattice3(sK0,sK2,sK3) | (~spl7_4 | ~spl7_5 | ~spl7_15 | ~spl7_21 | ~spl7_39)),
% 2.07/0.63    inference(subsumption_resolution,[],[f1531,f105])).
% 2.07/0.63  fof(f1531,plain,(
% 2.07/0.63    ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_lattice3(sK0,sK2,sK3) | (~spl7_4 | ~spl7_15 | ~spl7_21 | ~spl7_39)),
% 2.07/0.63    inference(duplicate_literal_removal,[],[f1526])).
% 2.07/0.63  fof(f1526,plain,(
% 2.07/0.63    ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_lattice3(sK0,sK2,sK3) | (~spl7_4 | ~spl7_15 | ~spl7_21 | ~spl7_39)),
% 2.07/0.63    inference(resolution,[],[f1520,f98])).
% 2.07/0.63  fof(f98,plain,(
% 2.07/0.63    ( ! [X24,X23] : (~r1_orders_2(sK0,sK6(sK0,X24,X23),X23) | ~m1_subset_1(X23,u1_struct_0(sK0)) | r2_lattice3(sK0,X24,X23)) ) | ~spl7_4),
% 2.07/0.63    inference(resolution,[],[f86,f59])).
% 2.07/0.63  fof(f59,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,sK6(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f22])).
% 2.07/0.63  fof(f22,plain,(
% 2.07/0.63    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.07/0.63    inference(flattening,[],[f21])).
% 2.07/0.63  fof(f21,plain,(
% 2.07/0.63    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.07/0.63    inference(ennf_transformation,[],[f8])).
% 2.07/0.63  fof(f8,axiom,(
% 2.07/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 2.07/0.63  fof(f1520,plain,(
% 2.07/0.63    ( ! [X0] : (r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0) | ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_4 | ~spl7_15 | ~spl7_21 | ~spl7_39)),
% 2.07/0.63    inference(subsumption_resolution,[],[f324,f477])).
% 2.07/0.63  fof(f477,plain,(
% 2.07/0.63    r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_39),
% 2.07/0.63    inference(avatar_component_clause,[],[f476])).
% 2.07/0.63  fof(f324,plain,(
% 2.07/0.63    ( ! [X0] : (~r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) | r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0)) ) | (~spl7_4 | ~spl7_15 | ~spl7_21)),
% 2.07/0.63    inference(subsumption_resolution,[],[f323,f86])).
% 2.07/0.63  fof(f323,plain,(
% 2.07/0.63    ( ! [X0] : (~l1_orders_2(sK0) | ~r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) | r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0)) ) | (~spl7_15 | ~spl7_21)),
% 2.07/0.63    inference(subsumption_resolution,[],[f321,f183])).
% 2.07/0.63  fof(f183,plain,(
% 2.07/0.63    m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl7_15),
% 2.07/0.63    inference(avatar_component_clause,[],[f181])).
% 2.07/0.63  fof(f321,plain,(
% 2.07/0.63    ( ! [X0] : (~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) | r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0)) ) | ~spl7_21),
% 2.07/0.63    inference(superposition,[],[f67,f267])).
% 2.07/0.63  fof(f267,plain,(
% 2.07/0.63    sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_21),
% 2.07/0.63    inference(avatar_component_clause,[],[f265])).
% 2.07/0.63  fof(f67,plain,(
% 2.07/0.63    ( ! [X0,X3,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,k1_yellow_0(X0,X1),X3)) )),
% 2.07/0.63    inference(equality_resolution,[],[f54])).
% 2.07/0.63  fof(f54,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 2.07/0.63    inference(cnf_transformation,[],[f20])).
% 2.07/0.63  fof(f20,plain,(
% 2.07/0.63    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.07/0.63    inference(flattening,[],[f19])).
% 2.07/0.63  fof(f19,plain,(
% 2.07/0.63    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.07/0.63    inference(ennf_transformation,[],[f9])).
% 2.07/0.63  fof(f9,axiom,(
% 2.07/0.63    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 2.07/0.63  fof(f1489,plain,(
% 2.07/0.63    ~spl7_13 | ~spl7_15 | spl7_39),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f1488])).
% 2.07/0.63  fof(f1488,plain,(
% 2.07/0.63    $false | (~spl7_13 | ~spl7_15 | spl7_39)),
% 2.07/0.63    inference(subsumption_resolution,[],[f1453,f163])).
% 2.07/0.63  fof(f163,plain,(
% 2.07/0.63    r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~spl7_13),
% 2.07/0.63    inference(avatar_component_clause,[],[f161])).
% 2.07/0.63  fof(f161,plain,(
% 2.07/0.63    spl7_13 <=> r2_hidden(sK6(sK0,sK2,sK3),sK2)),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 2.07/0.63  fof(f1453,plain,(
% 2.07/0.63    ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | (~spl7_15 | spl7_39)),
% 2.07/0.63    inference(subsumption_resolution,[],[f480,f183])).
% 2.07/0.63  fof(f480,plain,(
% 2.07/0.63    ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl7_39),
% 2.07/0.63    inference(resolution,[],[f478,f29])).
% 2.07/0.63  fof(f29,plain,(
% 2.07/0.63    ( ! [X4] : (r1_yellow_0(sK0,sK4(X4)) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 2.07/0.63    inference(cnf_transformation,[],[f16])).
% 2.07/0.63  fof(f16,plain,(
% 2.07/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r1_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.07/0.63    inference(flattening,[],[f15])).
% 2.07/0.63  fof(f15,plain,(
% 2.07/0.63    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r2_lattice3(X0,X1,X7) <~> r2_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k1_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r1_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.07/0.63    inference(ennf_transformation,[],[f14])).
% 2.07/0.63  fof(f14,plain,(
% 2.07/0.63    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k1_yellow_0(X0,X5) = X4 & r1_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r1_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X7) <=> r2_lattice3(X0,X2,X7)))))))),
% 2.07/0.63    inference(rectify,[],[f13])).
% 2.07/0.63  fof(f13,negated_conjecture,(
% 2.07/0.63    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 2.07/0.63    inference(negated_conjecture,[],[f12])).
% 2.07/0.63  fof(f12,conjecture,(
% 2.07/0.63    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k1_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k1_yellow_0(X0,X4) = X3 & r1_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r1_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) <=> r2_lattice3(X0,X2,X3)))))))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).
% 2.07/0.63  fof(f478,plain,(
% 2.07/0.63    ~r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | spl7_39),
% 2.07/0.63    inference(avatar_component_clause,[],[f476])).
% 2.07/0.63  fof(f1448,plain,(
% 2.07/0.63    ~spl7_4 | ~spl7_5 | spl7_9 | ~spl7_10 | ~spl7_22 | ~spl7_127),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f1447])).
% 2.07/0.63  fof(f1447,plain,(
% 2.07/0.63    $false | (~spl7_4 | ~spl7_5 | spl7_9 | ~spl7_10 | ~spl7_22 | ~spl7_127)),
% 2.07/0.63    inference(subsumption_resolution,[],[f1446,f128])).
% 2.07/0.63  fof(f128,plain,(
% 2.07/0.63    ~r2_lattice3(sK0,sK1,sK3) | spl7_9),
% 2.07/0.63    inference(avatar_component_clause,[],[f127])).
% 2.07/0.63  fof(f1446,plain,(
% 2.07/0.63    r2_lattice3(sK0,sK1,sK3) | (~spl7_4 | ~spl7_5 | ~spl7_10 | ~spl7_22 | ~spl7_127)),
% 2.07/0.63    inference(subsumption_resolution,[],[f1445,f133])).
% 2.07/0.63  fof(f133,plain,(
% 2.07/0.63    r2_lattice3(sK0,sK2,sK3) | ~spl7_10),
% 2.07/0.63    inference(avatar_component_clause,[],[f131])).
% 2.07/0.63  fof(f1445,plain,(
% 2.07/0.63    ~r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3) | (~spl7_4 | ~spl7_5 | ~spl7_22 | ~spl7_127)),
% 2.07/0.63    inference(subsumption_resolution,[],[f1444,f105])).
% 2.07/0.63  fof(f1444,plain,(
% 2.07/0.63    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3) | (~spl7_4 | ~spl7_22 | ~spl7_127)),
% 2.07/0.63    inference(subsumption_resolution,[],[f1437,f298])).
% 2.07/0.63  fof(f298,plain,(
% 2.07/0.63    m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | ~spl7_22),
% 2.07/0.63    inference(avatar_component_clause,[],[f296])).
% 2.07/0.63  fof(f296,plain,(
% 2.07/0.63    spl7_22 <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))),
% 2.07/0.63    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 2.07/0.64  fof(f1437,plain,(
% 2.07/0.64    ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3) | (~spl7_4 | ~spl7_127)),
% 2.07/0.64    inference(resolution,[],[f1434,f186])).
% 2.07/0.64  fof(f186,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~r2_hidden(sK6(sK0,X0,X1),X2) | ~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X2,X1) | r2_lattice3(sK0,X0,X1)) ) | ~spl7_4),
% 2.07/0.64    inference(duplicate_literal_removal,[],[f185])).
% 2.07/0.64  fof(f185,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~r2_hidden(sK6(sK0,X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl7_4),
% 2.07/0.64    inference(resolution,[],[f96,f98])).
% 2.07/0.64  fof(f96,plain,(
% 2.07/0.64    ( ! [X19,X20,X18] : (r1_orders_2(sK0,X19,X18) | ~m1_subset_1(X19,u1_struct_0(sK0)) | ~r2_hidden(X19,X20) | ~m1_subset_1(X18,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X20,X18)) ) | ~spl7_4),
% 2.07/0.64    inference(resolution,[],[f86,f56])).
% 2.07/0.64  fof(f56,plain,(
% 2.07/0.64    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  fof(f1434,plain,(
% 2.07/0.64    r2_hidden(sK6(sK0,sK1,sK3),sK2) | ~spl7_127),
% 2.07/0.64    inference(avatar_component_clause,[],[f1432])).
% 2.07/0.64  fof(f1432,plain,(
% 2.07/0.64    spl7_127 <=> r2_hidden(sK6(sK0,sK1,sK3),sK2)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_127])])).
% 2.07/0.64  fof(f1435,plain,(
% 2.07/0.64    spl7_127 | ~spl7_50 | ~spl7_122),
% 2.07/0.64    inference(avatar_split_clause,[],[f1413,f1342,f600,f1432])).
% 2.07/0.64  fof(f600,plain,(
% 2.07/0.64    spl7_50 <=> r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 2.07/0.64  fof(f1342,plain,(
% 2.07/0.64    spl7_122 <=> sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).
% 2.07/0.64  fof(f1413,plain,(
% 2.07/0.64    r2_hidden(sK6(sK0,sK1,sK3),sK2) | (~spl7_50 | ~spl7_122)),
% 2.07/0.64    inference(superposition,[],[f602,f1344])).
% 2.07/0.64  fof(f1344,plain,(
% 2.07/0.64    sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~spl7_122),
% 2.07/0.64    inference(avatar_component_clause,[],[f1342])).
% 2.07/0.64  fof(f602,plain,(
% 2.07/0.64    r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_50),
% 2.07/0.64    inference(avatar_component_clause,[],[f600])).
% 2.07/0.64  fof(f1388,plain,(
% 2.07/0.64    spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_22 | spl7_125),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f1387])).
% 2.07/0.64  fof(f1387,plain,(
% 2.07/0.64    $false | (spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_22 | spl7_125)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1380,f298])).
% 2.07/0.64  fof(f1380,plain,(
% 2.07/0.64    ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | (spl7_1 | ~spl7_2 | ~spl7_4 | spl7_125)),
% 2.07/0.64    inference(resolution,[],[f1378,f101])).
% 2.07/0.64  fof(f101,plain,(
% 2.07/0.64    ( ! [X25] : (r1_orders_2(sK0,X25,X25) | ~m1_subset_1(X25,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_4)),
% 2.07/0.64    inference(subsumption_resolution,[],[f100,f71])).
% 2.07/0.64  fof(f71,plain,(
% 2.07/0.64    ~v2_struct_0(sK0) | spl7_1),
% 2.07/0.64    inference(avatar_component_clause,[],[f69])).
% 2.07/0.64  fof(f69,plain,(
% 2.07/0.64    spl7_1 <=> v2_struct_0(sK0)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.07/0.64  fof(f100,plain,(
% 2.07/0.64    ( ! [X25] : (v2_struct_0(sK0) | ~m1_subset_1(X25,u1_struct_0(sK0)) | r1_orders_2(sK0,X25,X25)) ) | (~spl7_2 | ~spl7_4)),
% 2.07/0.64    inference(subsumption_resolution,[],[f99,f76])).
% 2.07/0.64  fof(f76,plain,(
% 2.07/0.64    v3_orders_2(sK0) | ~spl7_2),
% 2.07/0.64    inference(avatar_component_clause,[],[f74])).
% 2.07/0.64  fof(f74,plain,(
% 2.07/0.64    spl7_2 <=> v3_orders_2(sK0)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.07/0.64  fof(f99,plain,(
% 2.07/0.64    ( ! [X25] : (~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X25,u1_struct_0(sK0)) | r1_orders_2(sK0,X25,X25)) ) | ~spl7_4),
% 2.07/0.64    inference(resolution,[],[f86,f60])).
% 2.07/0.64  fof(f60,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f24])).
% 2.07/0.64  fof(f24,plain,(
% 2.07/0.64    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.07/0.64    inference(flattening,[],[f23])).
% 2.07/0.64  fof(f23,plain,(
% 2.07/0.64    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.07/0.64    inference(ennf_transformation,[],[f7])).
% 2.07/0.64  fof(f7,axiom,(
% 2.07/0.64    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 2.07/0.64  fof(f1378,plain,(
% 2.07/0.64    ~r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | spl7_125),
% 2.07/0.64    inference(avatar_component_clause,[],[f1376])).
% 2.07/0.64  fof(f1376,plain,(
% 2.07/0.64    spl7_125 <=> r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).
% 2.07/0.64  fof(f1379,plain,(
% 2.07/0.64    ~spl7_125 | ~spl7_4 | ~spl7_22 | spl7_121),
% 2.07/0.64    inference(avatar_split_clause,[],[f1353,f1338,f296,f84,f1376])).
% 2.07/0.64  fof(f1338,plain,(
% 2.07/0.64    spl7_121 <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_121])])).
% 2.07/0.64  fof(f1353,plain,(
% 2.07/0.64    ~r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | (~spl7_4 | ~spl7_22 | spl7_121)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1352,f298])).
% 2.07/0.64  fof(f1352,plain,(
% 2.07/0.64    ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | (~spl7_4 | spl7_121)),
% 2.07/0.64    inference(duplicate_literal_removal,[],[f1347])).
% 2.07/0.64  fof(f1347,plain,(
% 2.07/0.64    ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK6(sK0,sK1,sK3),sK6(sK0,sK1,sK3)) | ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | (~spl7_4 | spl7_121)),
% 2.07/0.64    inference(resolution,[],[f1340,f88])).
% 2.07/0.64  fof(f88,plain,(
% 2.07/0.64    ( ! [X0,X1] : (r2_lattice3(sK0,k1_tarski(X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_4),
% 2.07/0.64    inference(resolution,[],[f86,f45])).
% 2.07/0.64  fof(f45,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X1) | r2_lattice3(X0,k1_tarski(X2),X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f17])).
% 2.07/0.64  fof(f17,plain,(
% 2.07/0.64    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.07/0.64    inference(ennf_transformation,[],[f10])).
% 2.07/0.64  fof(f10,axiom,(
% 2.07/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 2.07/0.64  fof(f1340,plain,(
% 2.07/0.64    ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | spl7_121),
% 2.07/0.64    inference(avatar_component_clause,[],[f1338])).
% 2.07/0.64  fof(f1345,plain,(
% 2.07/0.64    ~spl7_121 | spl7_122 | ~spl7_4 | ~spl7_22 | ~spl7_26 | spl7_51 | ~spl7_102),
% 2.07/0.64    inference(avatar_split_clause,[],[f1336,f1147,f604,f354,f296,f84,f1342,f1338])).
% 2.07/0.64  fof(f354,plain,(
% 2.07/0.64    spl7_26 <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.07/0.64  fof(f604,plain,(
% 2.07/0.64    spl7_51 <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 2.07/0.64  fof(f1147,plain,(
% 2.07/0.64    spl7_102 <=> r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).
% 2.07/0.64  fof(f1336,plain,(
% 2.07/0.64    sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | (~spl7_4 | ~spl7_22 | ~spl7_26 | spl7_51 | ~spl7_102)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1335,f1148])).
% 2.07/0.64  fof(f1148,plain,(
% 2.07/0.64    r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~spl7_102),
% 2.07/0.64    inference(avatar_component_clause,[],[f1147])).
% 2.07/0.64  fof(f1335,plain,(
% 2.07/0.64    sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | ~r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_4 | ~spl7_22 | ~spl7_26 | spl7_51 | ~spl7_102)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1333,f298])).
% 2.07/0.64  fof(f1333,plain,(
% 2.07/0.64    ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | ~r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_4 | ~spl7_26 | spl7_51 | ~spl7_102)),
% 2.07/0.64    inference(duplicate_literal_removal,[],[f1329])).
% 2.07/0.64  fof(f1329,plain,(
% 2.07/0.64    ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | ~r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK6(sK0,sK1,sK3)) | ~m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | sK6(sK0,sK1,sK3) = k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_4 | ~spl7_26 | spl7_51 | ~spl7_102)),
% 2.07/0.64    inference(resolution,[],[f1326,f94])).
% 2.07/0.64  fof(f94,plain,(
% 2.07/0.64    ( ! [X14,X15] : (r2_lattice3(sK0,X15,sK5(sK0,X15,X14)) | ~r1_yellow_0(sK0,X15) | ~r2_lattice3(sK0,X15,X14) | ~m1_subset_1(X14,u1_struct_0(sK0)) | k1_yellow_0(sK0,X15) = X14) ) | ~spl7_4),
% 2.07/0.64    inference(resolution,[],[f86,f52])).
% 2.07/0.64  fof(f52,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | r2_lattice3(X0,X1,sK5(X0,X1,X2)) | k1_yellow_0(X0,X1) = X2) )),
% 2.07/0.64    inference(cnf_transformation,[],[f20])).
% 2.07/0.64  fof(f1326,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_lattice3(sK0,k1_tarski(X0),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0 | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)) ) | (~spl7_4 | ~spl7_26 | spl7_51 | ~spl7_102)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1094,f1148])).
% 2.07/0.64  fof(f1094,plain,(
% 2.07/0.64    ( ! [X0] : (k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(X0),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) ) | (~spl7_4 | ~spl7_26 | spl7_51)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1093,f86])).
% 2.07/0.64  fof(f1093,plain,(
% 2.07/0.64    ( ! [X0] : (k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(X0),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~l1_orders_2(sK0)) ) | (~spl7_4 | ~spl7_26 | spl7_51)),
% 2.07/0.64    inference(duplicate_literal_removal,[],[f1092])).
% 2.07/0.64  fof(f1092,plain,(
% 2.07/0.64    ( ! [X0] : (k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(X0),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~l1_orders_2(sK0) | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0) ) | (~spl7_4 | ~spl7_26 | spl7_51)),
% 2.07/0.64    inference(resolution,[],[f821,f51])).
% 2.07/0.64  fof(f51,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | k1_yellow_0(X0,X1) = X2) )),
% 2.07/0.64    inference(cnf_transformation,[],[f20])).
% 2.07/0.64  fof(f821,plain,(
% 2.07/0.64    ( ! [X3] : (~m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3),u1_struct_0(sK0)) | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(X3),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3)) ) | (~spl7_4 | ~spl7_26 | spl7_51)),
% 2.07/0.64    inference(duplicate_literal_removal,[],[f820])).
% 2.07/0.64  fof(f820,plain,(
% 2.07/0.64    ( ! [X3] : (~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3) | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(X3),sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3)) | ~m1_subset_1(sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X3),u1_struct_0(sK0))) ) | (~spl7_4 | ~spl7_26 | spl7_51)),
% 2.07/0.64    inference(resolution,[],[f812,f89])).
% 2.07/0.64  fof(f89,plain,(
% 2.07/0.64    ( ! [X2,X3] : (r1_orders_2(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_tarski(X3),X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl7_4),
% 2.07/0.64    inference(resolution,[],[f86,f46])).
% 2.07/0.64  fof(f46,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,k1_tarski(X2),X1) | r1_orders_2(X0,X2,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f17])).
% 2.07/0.64  fof(f812,plain,(
% 2.07/0.64    ( ! [X0] : (~r1_orders_2(sK0,X0,sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)) | ~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_4 | ~spl7_26 | spl7_51)),
% 2.07/0.64    inference(subsumption_resolution,[],[f364,f605])).
% 2.07/0.64  fof(f605,plain,(
% 2.07/0.64    k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3)) | spl7_51),
% 2.07/0.64    inference(avatar_component_clause,[],[f604])).
% 2.07/0.64  fof(f364,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~r1_orders_2(sK0,X0,sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)) | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))) ) | (~spl7_4 | ~spl7_26)),
% 2.07/0.64    inference(subsumption_resolution,[],[f360,f44])).
% 2.07/0.64  fof(f44,plain,(
% 2.07/0.64    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f6])).
% 2.07/0.64  fof(f6,axiom,(
% 2.07/0.64    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 2.07/0.64  fof(f360,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0) | ~r1_orders_2(sK0,X0,sK5(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X0)) | k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))) ) | (~spl7_4 | ~spl7_26)),
% 2.07/0.64    inference(resolution,[],[f356,f188])).
% 2.07/0.64  fof(f188,plain,(
% 2.07/0.64    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | ~r2_lattice3(sK0,X3,X2) | ~r1_orders_2(sK0,X2,sK5(sK0,X3,X2)) | k1_yellow_0(sK0,X3) = X2 | ~m1_subset_1(X2,u1_struct_0(sK0)) | k1_xboole_0 = X3 | ~v1_finset_1(X3)) ) | ~spl7_4),
% 2.07/0.64    inference(resolution,[],[f95,f35])).
% 2.07/0.64  fof(f35,plain,(
% 2.07/0.64    ( ! [X6] : (r1_yellow_0(sK0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK1)) | k1_xboole_0 = X6 | ~v1_finset_1(X6)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f95,plain,(
% 2.07/0.64    ( ! [X17,X16] : (~r1_yellow_0(sK0,X17) | ~m1_subset_1(X16,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X17,X16) | ~r1_orders_2(sK0,X16,sK5(sK0,X17,X16)) | k1_yellow_0(sK0,X17) = X16) ) | ~spl7_4),
% 2.07/0.64    inference(resolution,[],[f86,f53])).
% 2.07/0.64  fof(f53,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | k1_yellow_0(X0,X1) = X2) )),
% 2.07/0.64    inference(cnf_transformation,[],[f20])).
% 2.07/0.64  fof(f356,plain,(
% 2.07/0.64    m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~spl7_26),
% 2.07/0.64    inference(avatar_component_clause,[],[f354])).
% 2.07/0.64  fof(f1155,plain,(
% 2.07/0.64    ~spl7_26 | spl7_51 | spl7_102),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f1154])).
% 2.07/0.64  fof(f1154,plain,(
% 2.07/0.64    $false | (~spl7_26 | spl7_51 | spl7_102)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1153,f44])).
% 2.07/0.64  fof(f1153,plain,(
% 2.07/0.64    ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_26 | spl7_51 | spl7_102)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1152,f605])).
% 2.07/0.64  fof(f1152,plain,(
% 2.07/0.64    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_26 | spl7_102)),
% 2.07/0.64    inference(subsumption_resolution,[],[f1151,f356])).
% 2.07/0.64  fof(f1151,plain,(
% 2.07/0.64    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_102),
% 2.07/0.64    inference(resolution,[],[f1149,f35])).
% 2.07/0.64  fof(f1149,plain,(
% 2.07/0.64    ~r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | spl7_102),
% 2.07/0.64    inference(avatar_component_clause,[],[f1147])).
% 2.07/0.64  fof(f635,plain,(
% 2.07/0.64    ~spl7_51),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f634])).
% 2.07/0.64  fof(f634,plain,(
% 2.07/0.64    $false | ~spl7_51),
% 2.07/0.64    inference(subsumption_resolution,[],[f627,f42])).
% 2.07/0.64  fof(f42,plain,(
% 2.07/0.64    v1_xboole_0(k1_xboole_0)),
% 2.07/0.64    inference(cnf_transformation,[],[f1])).
% 2.07/0.64  fof(f1,axiom,(
% 2.07/0.64    v1_xboole_0(k1_xboole_0)),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.07/0.64  fof(f627,plain,(
% 2.07/0.64    ~v1_xboole_0(k1_xboole_0) | ~spl7_51),
% 2.07/0.64    inference(superposition,[],[f43,f606])).
% 2.07/0.64  fof(f606,plain,(
% 2.07/0.64    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~spl7_51),
% 2.07/0.64    inference(avatar_component_clause,[],[f604])).
% 2.07/0.64  fof(f43,plain,(
% 2.07/0.64    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f2])).
% 2.07/0.64  fof(f2,axiom,(
% 2.07/0.64    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 2.07/0.64  fof(f607,plain,(
% 2.07/0.64    spl7_50 | spl7_51 | ~spl7_26),
% 2.07/0.64    inference(avatar_split_clause,[],[f365,f354,f604,f600])).
% 2.07/0.64  fof(f365,plain,(
% 2.07/0.64    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_26),
% 2.07/0.64    inference(subsumption_resolution,[],[f361,f44])).
% 2.07/0.64  fof(f361,plain,(
% 2.07/0.64    ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_26),
% 2.07/0.64    inference(resolution,[],[f356,f34])).
% 2.07/0.64  fof(f34,plain,(
% 2.07/0.64    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | ~v1_finset_1(X3) | k1_xboole_0 = X3 | r2_hidden(k1_yellow_0(sK0,X3),sK2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f357,plain,(
% 2.07/0.64    spl7_26 | ~spl7_19),
% 2.07/0.64    inference(avatar_split_clause,[],[f282,f233,f354])).
% 2.07/0.64  fof(f233,plain,(
% 2.07/0.64    spl7_19 <=> r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 2.07/0.64  fof(f282,plain,(
% 2.07/0.64    m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~spl7_19),
% 2.07/0.64    inference(resolution,[],[f235,f63])).
% 2.07/0.64  fof(f63,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f4])).
% 2.07/0.64  fof(f4,axiom,(
% 2.07/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.07/0.64  fof(f235,plain,(
% 2.07/0.64    r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) | ~spl7_19),
% 2.07/0.64    inference(avatar_component_clause,[],[f233])).
% 2.07/0.64  fof(f331,plain,(
% 2.07/0.64    spl7_24 | ~spl7_23),
% 2.07/0.64    inference(avatar_split_clause,[],[f320,f313,f328])).
% 2.07/0.64  fof(f313,plain,(
% 2.07/0.64    spl7_23 <=> m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.07/0.64  fof(f320,plain,(
% 2.07/0.64    r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) | ~spl7_23),
% 2.07/0.64    inference(resolution,[],[f315,f64])).
% 2.07/0.64  fof(f64,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f4])).
% 2.07/0.64  fof(f315,plain,(
% 2.07/0.64    m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | ~spl7_23),
% 2.07/0.64    inference(avatar_component_clause,[],[f313])).
% 2.07/0.64  fof(f316,plain,(
% 2.07/0.64    spl7_23 | ~spl7_13 | ~spl7_15),
% 2.07/0.64    inference(avatar_split_clause,[],[f292,f181,f161,f313])).
% 2.07/0.64  fof(f292,plain,(
% 2.07/0.64    m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | (~spl7_13 | ~spl7_15)),
% 2.07/0.64    inference(subsumption_resolution,[],[f289,f183])).
% 2.07/0.64  fof(f289,plain,(
% 2.07/0.64    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | ~spl7_13),
% 2.07/0.64    inference(resolution,[],[f163,f28])).
% 2.07/0.64  fof(f28,plain,(
% 2.07/0.64    ( ! [X4] : (~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0)) | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1))) )),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f299,plain,(
% 2.07/0.64    spl7_22 | ~spl7_7 | ~spl7_12),
% 2.07/0.64    inference(avatar_split_clause,[],[f276,f148,f113,f296])).
% 2.07/0.64  fof(f113,plain,(
% 2.07/0.64    spl7_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.07/0.64  fof(f148,plain,(
% 2.07/0.64    spl7_12 <=> r2_hidden(sK6(sK0,sK1,sK3),sK1)),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.07/0.64  fof(f276,plain,(
% 2.07/0.64    m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) | (~spl7_7 | ~spl7_12)),
% 2.07/0.64    inference(resolution,[],[f150,f119])).
% 2.07/0.64  fof(f119,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_hidden(X0,sK1) | m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_7),
% 2.07/0.64    inference(resolution,[],[f115,f65])).
% 2.07/0.64  fof(f65,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f26])).
% 2.07/0.64  fof(f26,plain,(
% 2.07/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.07/0.64    inference(flattening,[],[f25])).
% 2.07/0.64  fof(f25,plain,(
% 2.07/0.64    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.07/0.64    inference(ennf_transformation,[],[f5])).
% 2.07/0.64  fof(f5,axiom,(
% 2.07/0.64    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 2.07/0.64  fof(f115,plain,(
% 2.07/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_7),
% 2.07/0.64    inference(avatar_component_clause,[],[f113])).
% 2.07/0.64  fof(f150,plain,(
% 2.07/0.64    r2_hidden(sK6(sK0,sK1,sK3),sK1) | ~spl7_12),
% 2.07/0.64    inference(avatar_component_clause,[],[f148])).
% 2.07/0.64  fof(f268,plain,(
% 2.07/0.64    spl7_21 | ~spl7_6 | ~spl7_13),
% 2.07/0.64    inference(avatar_split_clause,[],[f165,f161,f108,f265])).
% 2.07/0.64  fof(f108,plain,(
% 2.07/0.64    spl7_6 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.07/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.07/0.64  fof(f165,plain,(
% 2.07/0.64    sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | (~spl7_6 | ~spl7_13)),
% 2.07/0.64    inference(resolution,[],[f163,f142])).
% 2.07/0.64  fof(f142,plain,(
% 2.07/0.64    ( ! [X4] : (~r2_hidden(X4,sK2) | k1_yellow_0(sK0,sK4(X4)) = X4) ) | ~spl7_6),
% 2.07/0.64    inference(subsumption_resolution,[],[f30,f117])).
% 2.07/0.64  fof(f117,plain,(
% 2.07/0.64    ( ! [X0] : (~r2_hidden(X0,sK2) | m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_6),
% 2.07/0.64    inference(resolution,[],[f110,f65])).
% 2.07/0.64  fof(f110,plain,(
% 2.07/0.64    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_6),
% 2.07/0.64    inference(avatar_component_clause,[],[f108])).
% 2.07/0.64  fof(f30,plain,(
% 2.07/0.64    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | k1_yellow_0(sK0,sK4(X4)) = X4) )),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f236,plain,(
% 2.07/0.64    spl7_19 | ~spl7_12),
% 2.07/0.64    inference(avatar_split_clause,[],[f231,f148,f233])).
% 2.07/0.64  fof(f231,plain,(
% 2.07/0.64    r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) | ~spl7_12),
% 2.07/0.64    inference(resolution,[],[f150,f61])).
% 2.07/0.64  fof(f61,plain,(
% 2.07/0.64    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f3])).
% 2.07/0.64  fof(f3,axiom,(
% 2.07/0.64    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.07/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.07/0.64  fof(f184,plain,(
% 2.07/0.64    spl7_15 | ~spl7_6 | ~spl7_13),
% 2.07/0.64    inference(avatar_split_clause,[],[f166,f161,f108,f181])).
% 2.07/0.64  fof(f166,plain,(
% 2.07/0.64    m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | (~spl7_6 | ~spl7_13)),
% 2.07/0.64    inference(resolution,[],[f163,f117])).
% 2.07/0.64  fof(f164,plain,(
% 2.07/0.64    spl7_13 | ~spl7_4 | ~spl7_5 | spl7_10),
% 2.07/0.64    inference(avatar_split_clause,[],[f159,f131,f103,f84,f161])).
% 2.07/0.64  fof(f159,plain,(
% 2.07/0.64    r2_hidden(sK6(sK0,sK2,sK3),sK2) | (~spl7_4 | ~spl7_5 | spl7_10)),
% 2.07/0.64    inference(subsumption_resolution,[],[f157,f105])).
% 2.07/0.64  fof(f157,plain,(
% 2.07/0.64    r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_4 | spl7_10)),
% 2.07/0.64    inference(resolution,[],[f132,f97])).
% 2.07/0.64  fof(f97,plain,(
% 2.07/0.64    ( ! [X21,X22] : (r2_lattice3(sK0,X22,X21) | r2_hidden(sK6(sK0,X22,X21),X22) | ~m1_subset_1(X21,u1_struct_0(sK0))) ) | ~spl7_4),
% 2.07/0.64    inference(resolution,[],[f86,f58])).
% 2.07/0.64  fof(f58,plain,(
% 2.07/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK6(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2)) )),
% 2.07/0.64    inference(cnf_transformation,[],[f22])).
% 2.07/0.64  fof(f154,plain,(
% 2.07/0.64    ~spl7_9 | ~spl7_10),
% 2.07/0.64    inference(avatar_contradiction_clause,[],[f153])).
% 2.07/0.64  fof(f153,plain,(
% 2.07/0.64    $false | (~spl7_9 | ~spl7_10)),
% 2.07/0.64    inference(subsumption_resolution,[],[f152,f129])).
% 2.07/0.64  fof(f152,plain,(
% 2.07/0.64    ~r2_lattice3(sK0,sK1,sK3) | ~spl7_10),
% 2.07/0.64    inference(subsumption_resolution,[],[f32,f133])).
% 2.07/0.64  fof(f32,plain,(
% 2.07/0.64    ~r2_lattice3(sK0,sK2,sK3) | ~r2_lattice3(sK0,sK1,sK3)),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f151,plain,(
% 2.07/0.64    spl7_12 | ~spl7_4 | ~spl7_5 | spl7_9),
% 2.07/0.64    inference(avatar_split_clause,[],[f144,f127,f103,f84,f148])).
% 2.07/0.64  fof(f144,plain,(
% 2.07/0.64    r2_hidden(sK6(sK0,sK1,sK3),sK1) | (~spl7_4 | ~spl7_5 | spl7_9)),
% 2.07/0.64    inference(subsumption_resolution,[],[f143,f105])).
% 2.07/0.64  fof(f143,plain,(
% 2.07/0.64    r2_hidden(sK6(sK0,sK1,sK3),sK1) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_4 | spl7_9)),
% 2.07/0.64    inference(resolution,[],[f97,f128])).
% 2.07/0.64  fof(f134,plain,(
% 2.07/0.64    spl7_9 | spl7_10),
% 2.07/0.64    inference(avatar_split_clause,[],[f31,f131,f127])).
% 2.07/0.64  fof(f31,plain,(
% 2.07/0.64    r2_lattice3(sK0,sK2,sK3) | r2_lattice3(sK0,sK1,sK3)),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f116,plain,(
% 2.07/0.64    spl7_7),
% 2.07/0.64    inference(avatar_split_clause,[],[f37,f113])).
% 2.07/0.64  fof(f37,plain,(
% 2.07/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f111,plain,(
% 2.07/0.64    spl7_6),
% 2.07/0.64    inference(avatar_split_clause,[],[f36,f108])).
% 2.07/0.64  fof(f36,plain,(
% 2.07/0.64    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f106,plain,(
% 2.07/0.64    spl7_5),
% 2.07/0.64    inference(avatar_split_clause,[],[f33,f103])).
% 2.07/0.64  fof(f33,plain,(
% 2.07/0.64    m1_subset_1(sK3,u1_struct_0(sK0))),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f87,plain,(
% 2.07/0.64    spl7_4),
% 2.07/0.64    inference(avatar_split_clause,[],[f41,f84])).
% 2.07/0.64  fof(f41,plain,(
% 2.07/0.64    l1_orders_2(sK0)),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f77,plain,(
% 2.07/0.64    spl7_2),
% 2.07/0.64    inference(avatar_split_clause,[],[f39,f74])).
% 2.07/0.64  fof(f39,plain,(
% 2.07/0.64    v3_orders_2(sK0)),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  fof(f72,plain,(
% 2.07/0.64    ~spl7_1),
% 2.07/0.64    inference(avatar_split_clause,[],[f38,f69])).
% 2.07/0.64  fof(f38,plain,(
% 2.07/0.64    ~v2_struct_0(sK0)),
% 2.07/0.64    inference(cnf_transformation,[],[f16])).
% 2.07/0.64  % SZS output end Proof for theBenchmark
% 2.07/0.64  % (9689)------------------------------
% 2.07/0.64  % (9689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.64  % (9689)Termination reason: Refutation
% 2.07/0.64  
% 2.07/0.64  % (9689)Memory used [KB]: 11641
% 2.07/0.64  % (9689)Time elapsed: 0.188 s
% 2.07/0.64  % (9689)------------------------------
% 2.07/0.64  % (9689)------------------------------
% 2.07/0.64  % (9685)Success in time 0.275 s
%------------------------------------------------------------------------------
