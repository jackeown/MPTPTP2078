%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 361 expanded)
%              Number of leaves         :   36 ( 144 expanded)
%              Depth                    :   19
%              Number of atoms          :  645 (1651 expanded)
%              Number of equality atoms :   30 ( 165 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f63,f68,f72,f76,f82,f86,f91,f97,f101,f107,f112,f117,f121,f125,f129,f133,f137,f141,f153,f161,f166,f180,f189,f227,f231,f242,f247])).

fof(f247,plain,
    ( spl7_35
    | ~ spl7_18
    | spl7_33
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f245,f229,f225,f131,f236])).

fof(f236,plain,
    ( spl7_35
  <=> v1_xboole_0(k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f131,plain,
    ( spl7_18
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f225,plain,
    ( spl7_33
  <=> r2_hidden(sK3,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f229,plain,
    ( spl7_34
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f245,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | ~ spl7_18
    | spl7_33
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f244,f226])).

fof(f226,plain,
    ( ~ r2_hidden(sK3,k2_struct_0(sK2))
    | spl7_33 ),
    inference(avatar_component_clause,[],[f225])).

fof(f244,plain,
    ( r2_hidden(sK3,k2_struct_0(sK2))
    | v1_xboole_0(k2_struct_0(sK2))
    | ~ spl7_18
    | ~ spl7_34 ),
    inference(forward_demodulation,[],[f243,f230])).

fof(f230,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f229])).

fof(f243,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl7_18
    | ~ spl7_34 ),
    inference(forward_demodulation,[],[f167,f230])).

fof(f167,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl7_18 ),
    inference(resolution,[],[f132,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f132,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f242,plain,
    ( spl7_1
    | ~ spl7_26
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl7_1
    | ~ spl7_26
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f240,f54])).

fof(f54,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl7_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f240,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_26
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f239,f188])).

fof(f188,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl7_26
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f239,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_35 ),
    inference(resolution,[],[f237,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f237,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f236])).

fof(f231,plain,
    ( spl7_34
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f197,f187,f229])).

fof(f197,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl7_26 ),
    inference(resolution,[],[f188,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f227,plain,
    ( ~ spl7_33
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_16
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f223,f187,f159,f151,f139,f135,f131,f127,f123,f95,f84,f80,f225])).

fof(f80,plain,
    ( spl7_7
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f84,plain,
    ( spl7_8
  <=> r1_orders_2(sK1,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f95,plain,
    ( spl7_10
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f123,plain,
    ( spl7_16
  <=> m1_subset_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f127,plain,
    ( spl7_17
  <=> r1_orders_2(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f135,plain,
    ( spl7_19
  <=> m1_subset_1(sK4,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f139,plain,
    ( spl7_20
  <=> m1_subset_1(sK3,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f151,plain,
    ( spl7_21
  <=> v4_yellow_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f159,plain,
    ( spl7_22
  <=> m1_yellow_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f223,plain,
    ( ~ r2_hidden(sK3,k2_struct_0(sK2))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_16
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f222,f197])).

fof(f222,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_16
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f221,f128])).

fof(f128,plain,
    ( ~ r1_orders_2(sK2,sK3,sK4)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f127])).

fof(f221,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f220,f136])).

fof(f136,plain,
    ( m1_subset_1(sK4,k2_struct_0(sK1))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f135])).

fof(f220,plain,
    ( ~ m1_subset_1(sK4,k2_struct_0(sK1))
    | ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_16
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f219,f124])).

fof(f124,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f219,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k2_struct_0(sK1))
    | ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f218,f132])).

fof(f218,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k2_struct_0(sK1))
    | ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f217,f140])).

fof(f140,plain,
    ( m1_subset_1(sK3,k2_struct_0(sK1))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f139])).

fof(f217,plain,
    ( ~ m1_subset_1(sK3,k2_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k2_struct_0(sK1))
    | ~ r2_hidden(sK3,u1_struct_0(sK2))
    | r1_orders_2(sK2,sK3,sK4)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(resolution,[],[f172,f85])).

fof(f85,plain,
    ( r1_orders_2(sK1,sK3,sK4)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK1,X0,X1)
        | ~ m1_subset_1(X0,k2_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,k2_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,X1) )
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f171,f103])).

fof(f103,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl7_10 ),
    inference(resolution,[],[f96,f40])).

fof(f96,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,X1) )
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f170,f103])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,X1) )
    | ~ spl7_7
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f169,f81])).

fof(f81,plain,
    ( l1_orders_2(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,X1) )
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f168,f152])).

fof(f152,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f151])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ v4_yellow_0(sK2,sK1)
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_orders_2(sK1,X0,X1)
        | ~ r2_hidden(X0,u1_struct_0(sK2))
        | r1_orders_2(sK2,X0,X1) )
    | ~ spl7_22 ),
    inference(resolution,[],[f160,f50])).

fof(f50,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X5) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X3 != X5
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X5) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X2 != X4
      | X3 != X5
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r2_hidden(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).

fof(f160,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f159])).

fof(f189,plain,
    ( spl7_26
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f185,f178,f187])).

fof(f178,plain,
    ( spl7_24
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f185,plain,
    ( l1_struct_0(sK2)
    | ~ spl7_24 ),
    inference(resolution,[],[f179,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f179,plain,
    ( l1_orders_2(sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( spl7_24
    | ~ spl7_3
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f175,f164,f61,f178])).

fof(f61,plain,
    ( spl7_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f164,plain,
    ( spl7_23
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f175,plain,
    ( l1_orders_2(sK2)
    | ~ spl7_3
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f174,f62])).

fof(f62,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f174,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK2)
    | ~ spl7_23 ),
    inference(resolution,[],[f165,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f165,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f164])).

fof(f166,plain,
    ( spl7_23
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f157,f119,f74,f61,f164])).

fof(f74,plain,
    ( spl7_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f119,plain,
    ( spl7_15
  <=> m1_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f157,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f156,f62])).

fof(f156,plain,
    ( ~ l1_struct_0(sK0)
    | l1_waybel_0(sK2,sK0)
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f155,f75])).

fof(f75,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f155,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0)
    | l1_waybel_0(sK2,sK0)
    | ~ spl7_15 ),
    inference(resolution,[],[f120,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( l1_waybel_0(X2,X0)
          | ~ m1_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ! [X2] :
          ( m1_yellow_6(X2,X0,X1)
         => l1_waybel_0(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(f120,plain,
    ( m1_yellow_6(sK2,sK0,sK1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f119])).

fof(f161,plain,
    ( spl7_22
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f149,f119,f115,f74,f61,f159])).

fof(f115,plain,
    ( spl7_14
  <=> v2_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f149,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f148,f62])).

fof(f148,plain,
    ( m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f147,f120])).

fof(f147,plain,
    ( ~ m1_yellow_6(sK2,sK0,sK1)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f143,f75])).

fof(f143,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | m1_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl7_14 ),
    inference(resolution,[],[f116,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | m1_yellow_0(X2,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) )
              | ~ m1_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => ! [X2] :
              ( m1_yellow_6(X2,X0,X1)
             => ( v2_yellow_6(X2,X0,X1)
              <=> ( m1_yellow_0(X2,X1)
                  & v4_yellow_0(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_6)).

fof(f116,plain,
    ( v2_yellow_6(sK2,sK0,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f153,plain,
    ( spl7_21
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f146,f119,f115,f74,f61,f151])).

fof(f146,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f145,f62])).

fof(f145,plain,
    ( v4_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f144,f120])).

fof(f144,plain,
    ( ~ m1_yellow_6(sK2,sK0,sK1)
    | v4_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f142,f75])).

fof(f142,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_yellow_6(sK2,sK0,sK1)
    | v4_yellow_0(sK2,sK1)
    | ~ l1_struct_0(sK0)
    | ~ spl7_14 ),
    inference(resolution,[],[f116,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_yellow_6(X2,X0,X1)
      | v4_yellow_0(X2,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f141,plain,
    ( spl7_20
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f113,f110,f95,f139])).

fof(f110,plain,
    ( spl7_13
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f113,plain,
    ( m1_subset_1(sK3,k2_struct_0(sK1))
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f111,f103])).

fof(f111,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f137,plain,
    ( spl7_19
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f108,f105,f95,f135])).

fof(f105,plain,
    ( spl7_12
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f108,plain,
    ( m1_subset_1(sK4,k2_struct_0(sK1))
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f106,f103])).

fof(f106,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f133,plain,
    ( spl7_18
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f102,f99,f66,f131])).

fof(f66,plain,
    ( spl7_4
  <=> sK3 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f99,plain,
    ( spl7_11
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f102,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_4
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f100,f67])).

fof(f67,plain,
    ( sK3 = sK5
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f100,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f129,plain,
    ( ~ spl7_17
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(avatar_split_clause,[],[f93,f89,f70,f66,f127])).

fof(f70,plain,
    ( spl7_5
  <=> sK4 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f89,plain,
    ( spl7_9
  <=> r1_orders_2(sK2,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f93,plain,
    ( ~ r1_orders_2(sK2,sK3,sK4)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(forward_demodulation,[],[f92,f67])).

fof(f92,plain,
    ( ~ r1_orders_2(sK2,sK5,sK4)
    | ~ spl7_5
    | spl7_9 ),
    inference(forward_demodulation,[],[f90,f71])).

fof(f71,plain,
    ( sK4 = sK6
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f90,plain,
    ( ~ r1_orders_2(sK2,sK5,sK6)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f125,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f51,f123])).

fof(f51,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f25,f27])).

fof(f27,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1)
              & v2_yellow_6(X2,X0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_orders_2(X2,X5,X6)
                              & r1_orders_2(X1,X3,X4)
                              & X4 = X6
                              & X3 = X5
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_yellow_6(X2,X0,X1)
              & v2_yellow_6(X2,X0,X1)
              & ~ v2_struct_0(X2) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_yellow_6(X2,X0,X1)
                  & v2_yellow_6(X2,X0,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_orders_2(X1,X3,X4)
                                    & X4 = X6
                                    & X3 = X5 )
                                 => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_yellow_6(X2,X0,X1)
                & v2_yellow_6(X2,X0,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_orders_2(X1,X3,X4)
                                  & X4 = X6
                                  & X3 = X5 )
                               => r1_orders_2(X2,X5,X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_6)).

fof(f25,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f121,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f35,f119])).

fof(f35,plain,(
    m1_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f117,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f34,f115])).

fof(f34,plain,(
    v2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f112,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f32,f110])).

fof(f32,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f107,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f31,f105])).

fof(f31,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f30,f99])).

fof(f30,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f97,plain,
    ( spl7_10
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f87,f80,f95])).

fof(f87,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f81,f48])).

fof(f91,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f29,f89])).

fof(f29,plain,(
    ~ r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f28,f84])).

fof(f28,plain,(
    r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,
    ( spl7_7
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f78,f74,f61,f80])).

fof(f78,plain,
    ( l1_orders_2(sK1)
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f77,f62])).

fof(f77,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1)
    | ~ spl7_6 ),
    inference(resolution,[],[f75,f46])).

fof(f76,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f37,f74])).

fof(f37,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f27,f70])).

fof(f68,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f61])).

fof(f38,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f55,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f33,f53])).

fof(f33,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:46:14 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.45  % (8694)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.46  % (8701)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.47  % (8686)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.47  % (8686)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f248,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f55,f63,f68,f72,f76,f82,f86,f91,f97,f101,f107,f112,f117,f121,f125,f129,f133,f137,f141,f153,f161,f166,f180,f189,f227,f231,f242,f247])).
% 0.19/0.47  fof(f247,plain,(
% 0.19/0.47    spl7_35 | ~spl7_18 | spl7_33 | ~spl7_34),
% 0.19/0.47    inference(avatar_split_clause,[],[f245,f229,f225,f131,f236])).
% 0.19/0.47  fof(f236,plain,(
% 0.19/0.47    spl7_35 <=> v1_xboole_0(k2_struct_0(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.19/0.47  fof(f131,plain,(
% 0.19/0.47    spl7_18 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.19/0.47  fof(f225,plain,(
% 0.19/0.47    spl7_33 <=> r2_hidden(sK3,k2_struct_0(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.19/0.47  fof(f229,plain,(
% 0.19/0.47    spl7_34 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.19/0.47  fof(f245,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK2)) | (~spl7_18 | spl7_33 | ~spl7_34)),
% 0.19/0.47    inference(subsumption_resolution,[],[f244,f226])).
% 0.19/0.47  fof(f226,plain,(
% 0.19/0.47    ~r2_hidden(sK3,k2_struct_0(sK2)) | spl7_33),
% 0.19/0.47    inference(avatar_component_clause,[],[f225])).
% 0.19/0.47  fof(f244,plain,(
% 0.19/0.47    r2_hidden(sK3,k2_struct_0(sK2)) | v1_xboole_0(k2_struct_0(sK2)) | (~spl7_18 | ~spl7_34)),
% 0.19/0.47    inference(forward_demodulation,[],[f243,f230])).
% 0.19/0.47  fof(f230,plain,(
% 0.19/0.47    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_34),
% 0.19/0.47    inference(avatar_component_clause,[],[f229])).
% 0.19/0.47  fof(f243,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2)) | (~spl7_18 | ~spl7_34)),
% 0.19/0.47    inference(forward_demodulation,[],[f167,f230])).
% 0.19/0.47  fof(f167,plain,(
% 0.19/0.47    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2)) | ~spl7_18),
% 0.19/0.47    inference(resolution,[],[f132,f41])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.47    inference(flattening,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.47  fof(f132,plain,(
% 0.19/0.47    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl7_18),
% 0.19/0.47    inference(avatar_component_clause,[],[f131])).
% 0.19/0.47  fof(f242,plain,(
% 0.19/0.47    spl7_1 | ~spl7_26 | ~spl7_35),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f241])).
% 0.19/0.47  fof(f241,plain,(
% 0.19/0.47    $false | (spl7_1 | ~spl7_26 | ~spl7_35)),
% 0.19/0.47    inference(subsumption_resolution,[],[f240,f54])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ~v2_struct_0(sK2) | spl7_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f53])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    spl7_1 <=> v2_struct_0(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.19/0.47  fof(f240,plain,(
% 0.19/0.47    v2_struct_0(sK2) | (~spl7_26 | ~spl7_35)),
% 0.19/0.47    inference(subsumption_resolution,[],[f239,f188])).
% 0.19/0.47  fof(f188,plain,(
% 0.19/0.47    l1_struct_0(sK2) | ~spl7_26),
% 0.19/0.47    inference(avatar_component_clause,[],[f187])).
% 0.19/0.47  fof(f187,plain,(
% 0.19/0.47    spl7_26 <=> l1_struct_0(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.19/0.47  fof(f239,plain,(
% 0.19/0.47    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl7_35),
% 0.19/0.47    inference(resolution,[],[f237,f47])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.19/0.47  fof(f237,plain,(
% 0.19/0.47    v1_xboole_0(k2_struct_0(sK2)) | ~spl7_35),
% 0.19/0.47    inference(avatar_component_clause,[],[f236])).
% 0.19/0.47  fof(f231,plain,(
% 0.19/0.47    spl7_34 | ~spl7_26),
% 0.19/0.47    inference(avatar_split_clause,[],[f197,f187,f229])).
% 0.19/0.47  fof(f197,plain,(
% 0.19/0.47    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl7_26),
% 0.19/0.47    inference(resolution,[],[f188,f40])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.47  fof(f227,plain,(
% 0.19/0.47    ~spl7_33 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_16 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | ~spl7_22 | ~spl7_26),
% 0.19/0.47    inference(avatar_split_clause,[],[f223,f187,f159,f151,f139,f135,f131,f127,f123,f95,f84,f80,f225])).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    spl7_7 <=> l1_orders_2(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    spl7_8 <=> r1_orders_2(sK1,sK3,sK4)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.19/0.47  fof(f95,plain,(
% 0.19/0.47    spl7_10 <=> l1_struct_0(sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.19/0.47  fof(f123,plain,(
% 0.19/0.47    spl7_16 <=> m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    spl7_17 <=> r1_orders_2(sK2,sK3,sK4)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.19/0.47  fof(f135,plain,(
% 0.19/0.47    spl7_19 <=> m1_subset_1(sK4,k2_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.19/0.47  fof(f139,plain,(
% 0.19/0.47    spl7_20 <=> m1_subset_1(sK3,k2_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.19/0.47  fof(f151,plain,(
% 0.19/0.47    spl7_21 <=> v4_yellow_0(sK2,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.19/0.47  fof(f159,plain,(
% 0.19/0.47    spl7_22 <=> m1_yellow_0(sK2,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.19/0.47  fof(f223,plain,(
% 0.19/0.47    ~r2_hidden(sK3,k2_struct_0(sK2)) | (~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_16 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | ~spl7_22 | ~spl7_26)),
% 0.19/0.47    inference(forward_demodulation,[],[f222,f197])).
% 0.19/0.47  fof(f222,plain,(
% 0.19/0.47    ~r2_hidden(sK3,u1_struct_0(sK2)) | (~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_16 | spl7_17 | ~spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(subsumption_resolution,[],[f221,f128])).
% 0.19/0.47  fof(f128,plain,(
% 0.19/0.47    ~r1_orders_2(sK2,sK3,sK4) | spl7_17),
% 0.19/0.47    inference(avatar_component_clause,[],[f127])).
% 0.19/0.47  fof(f221,plain,(
% 0.19/0.47    ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4) | (~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_16 | ~spl7_18 | ~spl7_19 | ~spl7_20 | ~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(subsumption_resolution,[],[f220,f136])).
% 0.19/0.47  fof(f136,plain,(
% 0.19/0.47    m1_subset_1(sK4,k2_struct_0(sK1)) | ~spl7_19),
% 0.19/0.47    inference(avatar_component_clause,[],[f135])).
% 0.19/0.47  fof(f220,plain,(
% 0.19/0.47    ~m1_subset_1(sK4,k2_struct_0(sK1)) | ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4) | (~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_16 | ~spl7_18 | ~spl7_20 | ~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(subsumption_resolution,[],[f219,f124])).
% 0.19/0.47  fof(f124,plain,(
% 0.19/0.47    m1_subset_1(sK4,u1_struct_0(sK2)) | ~spl7_16),
% 0.19/0.47    inference(avatar_component_clause,[],[f123])).
% 0.19/0.47  fof(f219,plain,(
% 0.19/0.47    ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k2_struct_0(sK1)) | ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4) | (~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_18 | ~spl7_20 | ~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(subsumption_resolution,[],[f218,f132])).
% 0.19/0.47  fof(f218,plain,(
% 0.19/0.47    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k2_struct_0(sK1)) | ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4) | (~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_20 | ~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(subsumption_resolution,[],[f217,f140])).
% 0.19/0.47  fof(f140,plain,(
% 0.19/0.47    m1_subset_1(sK3,k2_struct_0(sK1)) | ~spl7_20),
% 0.19/0.47    inference(avatar_component_clause,[],[f139])).
% 0.19/0.47  fof(f217,plain,(
% 0.19/0.47    ~m1_subset_1(sK3,k2_struct_0(sK1)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k2_struct_0(sK1)) | ~r2_hidden(sK3,u1_struct_0(sK2)) | r1_orders_2(sK2,sK3,sK4) | (~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(resolution,[],[f172,f85])).
% 0.19/0.47  fof(f85,plain,(
% 0.19/0.47    r1_orders_2(sK1,sK3,sK4) | ~spl7_8),
% 0.19/0.47    inference(avatar_component_clause,[],[f84])).
% 0.19/0.47  fof(f172,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r1_orders_2(sK1,X0,X1) | ~m1_subset_1(X0,k2_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X1,k2_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,X1)) ) | (~spl7_7 | ~spl7_10 | ~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(forward_demodulation,[],[f171,f103])).
% 0.19/0.47  fof(f103,plain,(
% 0.19/0.47    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl7_10),
% 0.19/0.47    inference(resolution,[],[f96,f40])).
% 0.19/0.47  fof(f96,plain,(
% 0.19/0.47    l1_struct_0(sK1) | ~spl7_10),
% 0.19/0.47    inference(avatar_component_clause,[],[f95])).
% 0.19/0.47  fof(f171,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK1,X0,X1) | ~r2_hidden(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,X1)) ) | (~spl7_7 | ~spl7_10 | ~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(forward_demodulation,[],[f170,f103])).
% 0.19/0.47  fof(f170,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK1,X0,X1) | ~r2_hidden(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,X1)) ) | (~spl7_7 | ~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(subsumption_resolution,[],[f169,f81])).
% 0.19/0.47  fof(f81,plain,(
% 0.19/0.47    l1_orders_2(sK1) | ~spl7_7),
% 0.19/0.47    inference(avatar_component_clause,[],[f80])).
% 0.19/0.47  fof(f169,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~l1_orders_2(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK1,X0,X1) | ~r2_hidden(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,X1)) ) | (~spl7_21 | ~spl7_22)),
% 0.19/0.47    inference(subsumption_resolution,[],[f168,f152])).
% 0.19/0.47  fof(f152,plain,(
% 0.19/0.47    v4_yellow_0(sK2,sK1) | ~spl7_21),
% 0.19/0.47    inference(avatar_component_clause,[],[f151])).
% 0.19/0.47  fof(f168,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~v4_yellow_0(sK2,sK1) | ~l1_orders_2(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~r1_orders_2(sK1,X0,X1) | ~r2_hidden(X0,u1_struct_0(sK2)) | r1_orders_2(sK2,X0,X1)) ) | ~spl7_22),
% 0.19/0.47    inference(resolution,[],[f160,f50])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X4,X0,X5,X1] : (~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0) | ~l1_orders_2(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X5)) )),
% 0.19/0.47    inference(equality_resolution,[],[f49])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X4,X0,X5,X3,X1] : (~l1_orders_2(X0) | ~v4_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X1)) | X3 != X5 | ~r1_orders_2(X0,X4,X3) | ~r2_hidden(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X5)) )),
% 0.19/0.47    inference(equality_resolution,[],[f39])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~l1_orders_2(X0) | ~v4_yellow_0(X1,X0) | ~m1_yellow_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X1)) | X2 != X4 | X3 != X5 | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X5)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_orders_2(X1,X4,X5) | ~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4 | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0)) | ~l1_orders_2(X0))),
% 0.19/0.47    inference(flattening,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_orders_2(X1,X4,X5) | (~r2_hidden(X4,u1_struct_0(X1)) | ~r1_orders_2(X0,X2,X3) | X3 != X5 | X2 != X4)) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~m1_yellow_0(X1,X0) | ~v4_yellow_0(X1,X0))) | ~l1_orders_2(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0] : (l1_orders_2(X0) => ! [X1] : ((m1_yellow_0(X1,X0) & v4_yellow_0(X1,X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r2_hidden(X4,u1_struct_0(X1)) & r1_orders_2(X0,X2,X3) & X3 = X5 & X2 = X4) => r1_orders_2(X1,X4,X5))))))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).
% 0.19/0.47  fof(f160,plain,(
% 0.19/0.47    m1_yellow_0(sK2,sK1) | ~spl7_22),
% 0.19/0.47    inference(avatar_component_clause,[],[f159])).
% 0.19/0.47  fof(f189,plain,(
% 0.19/0.47    spl7_26 | ~spl7_24),
% 0.19/0.47    inference(avatar_split_clause,[],[f185,f178,f187])).
% 0.19/0.47  fof(f178,plain,(
% 0.19/0.47    spl7_24 <=> l1_orders_2(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.19/0.47  fof(f185,plain,(
% 0.19/0.47    l1_struct_0(sK2) | ~spl7_24),
% 0.19/0.47    inference(resolution,[],[f179,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.19/0.47  fof(f179,plain,(
% 0.19/0.47    l1_orders_2(sK2) | ~spl7_24),
% 0.19/0.47    inference(avatar_component_clause,[],[f178])).
% 0.19/0.47  fof(f180,plain,(
% 0.19/0.47    spl7_24 | ~spl7_3 | ~spl7_23),
% 0.19/0.47    inference(avatar_split_clause,[],[f175,f164,f61,f178])).
% 0.19/0.47  fof(f61,plain,(
% 0.19/0.47    spl7_3 <=> l1_struct_0(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.19/0.47  fof(f164,plain,(
% 0.19/0.47    spl7_23 <=> l1_waybel_0(sK2,sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.19/0.47  fof(f175,plain,(
% 0.19/0.47    l1_orders_2(sK2) | (~spl7_3 | ~spl7_23)),
% 0.19/0.47    inference(subsumption_resolution,[],[f174,f62])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    l1_struct_0(sK0) | ~spl7_3),
% 0.19/0.47    inference(avatar_component_clause,[],[f61])).
% 0.19/0.47  fof(f174,plain,(
% 0.19/0.47    ~l1_struct_0(sK0) | l1_orders_2(sK2) | ~spl7_23),
% 0.19/0.47    inference(resolution,[],[f165,f46])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.19/0.47  fof(f165,plain,(
% 0.19/0.47    l1_waybel_0(sK2,sK0) | ~spl7_23),
% 0.19/0.47    inference(avatar_component_clause,[],[f164])).
% 0.19/0.47  fof(f166,plain,(
% 0.19/0.47    spl7_23 | ~spl7_3 | ~spl7_6 | ~spl7_15),
% 0.19/0.47    inference(avatar_split_clause,[],[f157,f119,f74,f61,f164])).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    spl7_6 <=> l1_waybel_0(sK1,sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.19/0.47  fof(f119,plain,(
% 0.19/0.47    spl7_15 <=> m1_yellow_6(sK2,sK0,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.19/0.47  fof(f157,plain,(
% 0.19/0.47    l1_waybel_0(sK2,sK0) | (~spl7_3 | ~spl7_6 | ~spl7_15)),
% 0.19/0.47    inference(subsumption_resolution,[],[f156,f62])).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    ~l1_struct_0(sK0) | l1_waybel_0(sK2,sK0) | (~spl7_6 | ~spl7_15)),
% 0.19/0.47    inference(subsumption_resolution,[],[f155,f75])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    l1_waybel_0(sK1,sK0) | ~spl7_6),
% 0.19/0.47    inference(avatar_component_clause,[],[f74])).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0) | l1_waybel_0(sK2,sK0) | ~spl7_15),
% 0.19/0.47    inference(resolution,[],[f120,f42])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_waybel_0(X2,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0,X1] : (! [X2] : (l1_waybel_0(X2,X0) | ~m1_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => ! [X2] : (m1_yellow_6(X2,X0,X1) => l1_waybel_0(X2,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).
% 0.19/0.47  fof(f120,plain,(
% 0.19/0.47    m1_yellow_6(sK2,sK0,sK1) | ~spl7_15),
% 0.19/0.47    inference(avatar_component_clause,[],[f119])).
% 0.19/0.47  fof(f161,plain,(
% 0.19/0.47    spl7_22 | ~spl7_3 | ~spl7_6 | ~spl7_14 | ~spl7_15),
% 0.19/0.47    inference(avatar_split_clause,[],[f149,f119,f115,f74,f61,f159])).
% 0.19/0.47  fof(f115,plain,(
% 0.19/0.47    spl7_14 <=> v2_yellow_6(sK2,sK0,sK1)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.19/0.47  fof(f149,plain,(
% 0.19/0.47    m1_yellow_0(sK2,sK1) | (~spl7_3 | ~spl7_6 | ~spl7_14 | ~spl7_15)),
% 0.19/0.47    inference(subsumption_resolution,[],[f148,f62])).
% 0.19/0.47  fof(f148,plain,(
% 0.19/0.47    m1_yellow_0(sK2,sK1) | ~l1_struct_0(sK0) | (~spl7_6 | ~spl7_14 | ~spl7_15)),
% 0.19/0.47    inference(subsumption_resolution,[],[f147,f120])).
% 0.19/0.47  fof(f147,plain,(
% 0.19/0.47    ~m1_yellow_6(sK2,sK0,sK1) | m1_yellow_0(sK2,sK1) | ~l1_struct_0(sK0) | (~spl7_6 | ~spl7_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f143,f75])).
% 0.19/0.47  fof(f143,plain,(
% 0.19/0.47    ~l1_waybel_0(sK1,sK0) | ~m1_yellow_6(sK2,sK0,sK1) | m1_yellow_0(sK2,sK1) | ~l1_struct_0(sK0) | ~spl7_14),
% 0.19/0.47    inference(resolution,[],[f116,f44])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~m1_yellow_6(X2,X0,X1) | m1_yellow_0(X2,X1) | ~l1_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (! [X2] : ((v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))) | ~m1_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => ! [X2] : (m1_yellow_6(X2,X0,X1) => (v2_yellow_6(X2,X0,X1) <=> (m1_yellow_0(X2,X1) & v4_yellow_0(X2,X1))))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_6)).
% 0.19/0.47  fof(f116,plain,(
% 0.19/0.47    v2_yellow_6(sK2,sK0,sK1) | ~spl7_14),
% 0.19/0.47    inference(avatar_component_clause,[],[f115])).
% 0.19/0.47  fof(f153,plain,(
% 0.19/0.47    spl7_21 | ~spl7_3 | ~spl7_6 | ~spl7_14 | ~spl7_15),
% 0.19/0.47    inference(avatar_split_clause,[],[f146,f119,f115,f74,f61,f151])).
% 0.19/0.47  fof(f146,plain,(
% 0.19/0.47    v4_yellow_0(sK2,sK1) | (~spl7_3 | ~spl7_6 | ~spl7_14 | ~spl7_15)),
% 0.19/0.47    inference(subsumption_resolution,[],[f145,f62])).
% 0.19/0.47  fof(f145,plain,(
% 0.19/0.47    v4_yellow_0(sK2,sK1) | ~l1_struct_0(sK0) | (~spl7_6 | ~spl7_14 | ~spl7_15)),
% 0.19/0.47    inference(subsumption_resolution,[],[f144,f120])).
% 0.19/0.47  fof(f144,plain,(
% 0.19/0.47    ~m1_yellow_6(sK2,sK0,sK1) | v4_yellow_0(sK2,sK1) | ~l1_struct_0(sK0) | (~spl7_6 | ~spl7_14)),
% 0.19/0.47    inference(subsumption_resolution,[],[f142,f75])).
% 0.19/0.47  fof(f142,plain,(
% 0.19/0.47    ~l1_waybel_0(sK1,sK0) | ~m1_yellow_6(sK2,sK0,sK1) | v4_yellow_0(sK2,sK1) | ~l1_struct_0(sK0) | ~spl7_14),
% 0.19/0.47    inference(resolution,[],[f116,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v2_yellow_6(X2,X0,X1) | ~l1_waybel_0(X1,X0) | ~m1_yellow_6(X2,X0,X1) | v4_yellow_0(X2,X1) | ~l1_struct_0(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f141,plain,(
% 0.19/0.47    spl7_20 | ~spl7_10 | ~spl7_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f113,f110,f95,f139])).
% 0.19/0.47  fof(f110,plain,(
% 0.19/0.47    spl7_13 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.19/0.47  fof(f113,plain,(
% 0.19/0.47    m1_subset_1(sK3,k2_struct_0(sK1)) | (~spl7_10 | ~spl7_13)),
% 0.19/0.47    inference(forward_demodulation,[],[f111,f103])).
% 0.19/0.47  fof(f111,plain,(
% 0.19/0.47    m1_subset_1(sK3,u1_struct_0(sK1)) | ~spl7_13),
% 0.19/0.47    inference(avatar_component_clause,[],[f110])).
% 0.19/0.47  fof(f137,plain,(
% 0.19/0.47    spl7_19 | ~spl7_10 | ~spl7_12),
% 0.19/0.47    inference(avatar_split_clause,[],[f108,f105,f95,f135])).
% 0.19/0.47  fof(f105,plain,(
% 0.19/0.47    spl7_12 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.19/0.47  fof(f108,plain,(
% 0.19/0.47    m1_subset_1(sK4,k2_struct_0(sK1)) | (~spl7_10 | ~spl7_12)),
% 0.19/0.47    inference(forward_demodulation,[],[f106,f103])).
% 0.19/0.47  fof(f106,plain,(
% 0.19/0.47    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl7_12),
% 0.19/0.47    inference(avatar_component_clause,[],[f105])).
% 0.19/0.47  fof(f133,plain,(
% 0.19/0.47    spl7_18 | ~spl7_4 | ~spl7_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f102,f99,f66,f131])).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    spl7_4 <=> sK3 = sK5),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.19/0.47  fof(f99,plain,(
% 0.19/0.47    spl7_11 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.19/0.47  fof(f102,plain,(
% 0.19/0.47    m1_subset_1(sK3,u1_struct_0(sK2)) | (~spl7_4 | ~spl7_11)),
% 0.19/0.47    inference(forward_demodulation,[],[f100,f67])).
% 0.19/0.47  fof(f67,plain,(
% 0.19/0.47    sK3 = sK5 | ~spl7_4),
% 0.19/0.47    inference(avatar_component_clause,[],[f66])).
% 0.19/0.47  fof(f100,plain,(
% 0.19/0.47    m1_subset_1(sK5,u1_struct_0(sK2)) | ~spl7_11),
% 0.19/0.47    inference(avatar_component_clause,[],[f99])).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    ~spl7_17 | ~spl7_4 | ~spl7_5 | spl7_9),
% 0.19/0.47    inference(avatar_split_clause,[],[f93,f89,f70,f66,f127])).
% 0.19/0.47  fof(f70,plain,(
% 0.19/0.47    spl7_5 <=> sK4 = sK6),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    spl7_9 <=> r1_orders_2(sK2,sK5,sK6)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.19/0.47  fof(f93,plain,(
% 0.19/0.47    ~r1_orders_2(sK2,sK3,sK4) | (~spl7_4 | ~spl7_5 | spl7_9)),
% 0.19/0.47    inference(forward_demodulation,[],[f92,f67])).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    ~r1_orders_2(sK2,sK5,sK4) | (~spl7_5 | spl7_9)),
% 0.19/0.47    inference(forward_demodulation,[],[f90,f71])).
% 0.19/0.47  fof(f71,plain,(
% 0.19/0.47    sK4 = sK6 | ~spl7_5),
% 0.19/0.47    inference(avatar_component_clause,[],[f70])).
% 0.19/0.47  fof(f90,plain,(
% 0.19/0.47    ~r1_orders_2(sK2,sK5,sK6) | spl7_9),
% 0.19/0.47    inference(avatar_component_clause,[],[f89])).
% 0.19/0.47  fof(f125,plain,(
% 0.19/0.47    spl7_16),
% 0.19/0.47    inference(avatar_split_clause,[],[f51,f123])).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.19/0.47    inference(forward_demodulation,[],[f25,f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    sK4 = sK6),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_orders_2(X2,X5,X6) & r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.19/0.47    inference(flattening,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_orders_2(X2,X5,X6) & (r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X2))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) & (m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,negated_conjecture,(
% 0.19/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5) => r1_orders_2(X2,X5,X6)))))))))),
% 0.19/0.47    inference(negated_conjecture,[],[f9])).
% 0.19/0.47  fof(f9,conjecture,(
% 0.19/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_yellow_6(X2,X0,X1) & v2_yellow_6(X2,X0,X1) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_orders_2(X1,X3,X4) & X4 = X6 & X3 = X5) => r1_orders_2(X2,X5,X6)))))))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_6)).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f121,plain,(
% 0.19/0.47    spl7_15),
% 0.19/0.47    inference(avatar_split_clause,[],[f35,f119])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    m1_yellow_6(sK2,sK0,sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f117,plain,(
% 0.19/0.47    spl7_14),
% 0.19/0.47    inference(avatar_split_clause,[],[f34,f115])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    v2_yellow_6(sK2,sK0,sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f112,plain,(
% 0.19/0.47    spl7_13),
% 0.19/0.47    inference(avatar_split_clause,[],[f32,f110])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f107,plain,(
% 0.19/0.47    spl7_12),
% 0.19/0.47    inference(avatar_split_clause,[],[f31,f105])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f101,plain,(
% 0.19/0.47    spl7_11),
% 0.19/0.47    inference(avatar_split_clause,[],[f30,f99])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f97,plain,(
% 0.19/0.47    spl7_10 | ~spl7_7),
% 0.19/0.47    inference(avatar_split_clause,[],[f87,f80,f95])).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    l1_struct_0(sK1) | ~spl7_7),
% 0.19/0.47    inference(resolution,[],[f81,f48])).
% 0.19/0.47  fof(f91,plain,(
% 0.19/0.47    ~spl7_9),
% 0.19/0.47    inference(avatar_split_clause,[],[f29,f89])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ~r1_orders_2(sK2,sK5,sK6)),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f86,plain,(
% 0.19/0.47    spl7_8),
% 0.19/0.47    inference(avatar_split_clause,[],[f28,f84])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    r1_orders_2(sK1,sK3,sK4)),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    spl7_7 | ~spl7_3 | ~spl7_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f78,f74,f61,f80])).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    l1_orders_2(sK1) | (~spl7_3 | ~spl7_6)),
% 0.19/0.47    inference(subsumption_resolution,[],[f77,f62])).
% 0.19/0.47  fof(f77,plain,(
% 0.19/0.47    ~l1_struct_0(sK0) | l1_orders_2(sK1) | ~spl7_6),
% 0.19/0.47    inference(resolution,[],[f75,f46])).
% 0.19/0.47  fof(f76,plain,(
% 0.19/0.47    spl7_6),
% 0.19/0.47    inference(avatar_split_clause,[],[f37,f74])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    l1_waybel_0(sK1,sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f72,plain,(
% 0.19/0.47    spl7_5),
% 0.19/0.47    inference(avatar_split_clause,[],[f27,f70])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    spl7_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f26,f66])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    sK3 = sK5),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    spl7_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f38,f61])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    l1_struct_0(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ~spl7_1),
% 0.19/0.47    inference(avatar_split_clause,[],[f33,f53])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ~v2_struct_0(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (8686)------------------------------
% 0.19/0.47  % (8686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (8686)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (8686)Memory used [KB]: 6268
% 0.19/0.47  % (8686)Time elapsed: 0.059 s
% 0.19/0.47  % (8686)------------------------------
% 0.19/0.47  % (8686)------------------------------
% 0.19/0.47  % (8693)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.48  % (8697)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.48  % (8700)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.48  % (8691)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.49  % (8692)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.49  % (8685)Success in time 0.145 s
%------------------------------------------------------------------------------
