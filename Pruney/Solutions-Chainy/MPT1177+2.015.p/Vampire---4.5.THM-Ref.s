%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 514 expanded)
%              Number of leaves         :   50 ( 225 expanded)
%              Depth                    :   14
%              Number of atoms          : 1060 (2767 expanded)
%              Number of equality atoms :   74 ( 102 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f969,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f133,f138,f143,f148,f157,f159,f213,f237,f251,f276,f286,f291,f297,f314,f319,f343,f357,f383,f394,f401,f428,f494,f649,f863,f880,f951,f968])).

fof(f968,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_53 ),
    inference(avatar_contradiction_clause,[],[f963])).

fof(f963,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_53 ),
    inference(unit_resulting_resolution,[],[f112,f117,f122,f127,f132,f541,f950,f147,f950,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(f147,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl5_8
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f950,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f948])).

fof(f948,plain,
    ( spl5_53
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f541,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f534])).

fof(f534,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f99,f462])).

fof(f462,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(resolution,[],[f453,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,sK4(k4_xboole_0(X0,X1))))
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f103,f160])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK4(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f82,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f453,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(subsumption_resolution,[],[f449,f86])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f449,plain,(
    ! [X4,X3] :
      ( r1_tarski(k1_xboole_0,X4)
      | ~ r1_tarski(X3,k2_xboole_0(X3,X4)) ) ),
    inference(superposition,[],[f103,f414])).

fof(f414,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f176,f86])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f132,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f127,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f122,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f117,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f112,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f951,plain,
    ( spl5_53
    | ~ spl5_6
    | ~ spl5_25
    | ~ spl5_30
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f938,f426,f380,f316,f135,f948])).

fof(f135,plain,
    ( spl5_6
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f316,plain,
    ( spl5_25
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f380,plain,
    ( spl5_30
  <=> m1_orders_2(sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f426,plain,
    ( spl5_33
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f938,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_6
    | ~ spl5_25
    | ~ spl5_30
    | ~ spl5_33 ),
    inference(backward_demodulation,[],[f137,f936])).

fof(f936,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_25
    | ~ spl5_30
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f932,f318])).

fof(f318,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f316])).

fof(f932,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_30
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f922,f382])).

fof(f382,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f380])).

fof(f922,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_30
    | ~ spl5_33 ),
    inference(resolution,[],[f382,f427])).

fof(f427,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X1,sK0,X0)
        | ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f426])).

fof(f137,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f880,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_21
    | spl5_31
    | ~ spl5_52 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_21
    | spl5_31
    | ~ spl5_52 ),
    inference(unit_resulting_resolution,[],[f112,f117,f122,f127,f132,f393,f290,f862,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X2,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f862,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f860])).

fof(f860,plain,
    ( spl5_52
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f290,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl5_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f393,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl5_31
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f863,plain,
    ( spl5_52
    | spl5_29
    | ~ spl5_7
    | spl5_10
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f672,f647,f154,f140,f375,f860])).

fof(f375,plain,
    ( spl5_29
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f140,plain,
    ( spl5_7
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f154,plain,
    ( spl5_10
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f647,plain,
    ( spl5_43
  <=> ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK2 = X0
        | m1_orders_2(X0,sK0,sK2)
        | m1_orders_2(sK2,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f672,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | ~ spl5_7
    | spl5_10
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f670,f155])).

fof(f155,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f670,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | ~ spl5_7
    | ~ spl5_43 ),
    inference(resolution,[],[f648,f142])).

fof(f142,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f648,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK2 = X0
        | m1_orders_2(X0,sK0,sK2)
        | m1_orders_2(sK2,sK0,X0) )
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f647])).

fof(f649,plain,
    ( spl5_43
    | ~ spl5_6
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f497,f492,f135,f647])).

fof(f492,plain,
    ( spl5_37
  <=> ! [X1,X0] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f497,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | sK2 = X0
        | m1_orders_2(X0,sK0,sK2)
        | m1_orders_2(sK2,sK0,X0) )
    | ~ spl5_6
    | ~ spl5_37 ),
    inference(resolution,[],[f493,f137])).

fof(f493,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | ~ m2_orders_2(X0,sK0,sK1)
        | X0 = X1
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f492])).

fof(f494,plain,
    ( spl5_37
    | ~ spl5_8
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f323,f312,f145,f492])).

fof(f312,plain,
    ( spl5_24
  <=> ! [X1,X0,X2] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f323,plain,
    ( ! [X0,X1] :
        ( X0 = X1
        | ~ m2_orders_2(X0,sK0,sK1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl5_8
    | ~ spl5_24 ),
    inference(resolution,[],[f313,f147])).

fof(f313,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f312])).

fof(f428,plain,
    ( spl5_33
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f292,f284,f426])).

fof(f284,plain,
    ( spl5_20
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl5_20 ),
    inference(resolution,[],[f285,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_orders_2(X1,sK0,X0) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f284])).

fof(f401,plain,
    ( ~ spl5_9
    | ~ spl5_29 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f399,f85])).

fof(f85,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f399,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl5_9
    | ~ spl5_29 ),
    inference(backward_demodulation,[],[f152,f377])).

fof(f377,plain,
    ( sK2 = sK3
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f375])).

fof(f152,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_9
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f394,plain,
    ( ~ spl5_31
    | spl5_29
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f384,f150,f375,f391])).

fof(f384,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f152,f166])).

fof(f166,plain,(
    ! [X4,X3] :
      ( ~ r2_xboole_0(X4,X3)
      | X3 = X4
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f94,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f383,plain,
    ( spl5_30
    | spl5_9
    | ~ spl5_10
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f369,f354,f154,f150,f380])).

fof(f354,plain,
    ( spl5_27
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f369,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | spl5_9
    | ~ spl5_10
    | ~ spl5_27 ),
    inference(backward_demodulation,[],[f156,f365])).

fof(f365,plain,
    ( sK2 = sK3
    | spl5_9
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f363,f151])).

fof(f151,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f363,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl5_27 ),
    inference(resolution,[],[f356,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f356,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f354])).

fof(f156,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f357,plain,
    ( spl5_27
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f352,f340,f235,f154,f354])).

fof(f235,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | r1_tarski(X0,X1)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f340,plain,
    ( spl5_26
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f352,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f351,f342])).

fof(f342,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f340])).

fof(f351,plain,
    ( r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(resolution,[],[f236,f156])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | r1_tarski(X0,X1)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f235])).

fof(f343,plain,
    ( spl5_26
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f327,f294,f340])).

fof(f294,plain,
    ( spl5_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f327,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl5_22 ),
    inference(resolution,[],[f296,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f296,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f294])).

fof(f319,plain,
    ( spl5_25
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f305,f288,f316])).

fof(f305,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_21 ),
    inference(resolution,[],[f290,f100])).

fof(f314,plain,
    ( spl5_24
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f233,f130,f125,f120,f115,f110,f312])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f232,f112])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f231,f117])).

fof(f231,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f230,f122])).

fof(f230,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f229,f127])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f79,f132])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_orders_2(X2,X0,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

fof(f297,plain,
    ( spl5_22
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f282,f274,f140,f294])).

fof(f274,plain,
    ( spl5_19
  <=> ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f282,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(resolution,[],[f275,f142])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f274])).

fof(f291,plain,
    ( spl5_21
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f281,f274,f135,f288])).

fof(f281,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(resolution,[],[f275,f137])).

fof(f286,plain,
    ( spl5_20
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f218,f130,f125,f120,f115,f110,f284])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f217,f112])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f216,f117])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f215,f122])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f214,f127])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f209,f132])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f81,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(f276,plain,
    ( spl5_19
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f266,f249,f145,f274])).

fof(f249,plain,
    ( spl5_15
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(resolution,[],[f250,f147])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f249])).

fof(f251,plain,
    ( spl5_15
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f197,f130,f125,f120,f115,f110,f249])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f196,f112])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f195,f117])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f194,f122])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f193,f127])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f90,f132])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f237,plain,
    ( spl5_13
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f228,f211,f235])).

fof(f211,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | r1_tarski(X0,X1)
        | ~ r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl5_11 ),
    inference(resolution,[],[f212,f101])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,X1)
        | r1_tarski(X0,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f211])).

fof(f213,plain,
    ( spl5_11
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f186,f130,f125,f120,f115,f110,f211])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f185,f112])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f184,f117])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f183,f122])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f182,f127])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,X1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f80,f132])).

fof(f159,plain,
    ( ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f158,f154,f150])).

fof(f158,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f74,f156])).

fof(f74,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f54,f53,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

fof(f157,plain,
    ( spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f73,f154,f150])).

fof(f73,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f148,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f70,f145])).

fof(f70,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f143,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f72,f140])).

fof(f72,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f138,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f71,f135])).

fof(f71,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f133,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f69,f130])).

fof(f69,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f128,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f68,f125])).

fof(f68,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f123,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f67,f120])).

fof(f67,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f118,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f66,f115])).

fof(f66,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f113,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f65,f110])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:15:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (15520)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (15534)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (15536)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (15539)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (15531)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (15523)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (15522)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (15521)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (15542)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (15526)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (15518)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (15528)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (15519)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (15541)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (15517)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (15540)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (15522)Refutation not found, incomplete strategy% (15522)------------------------------
% 0.22/0.53  % (15522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15522)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (15522)Memory used [KB]: 6140
% 0.22/0.53  % (15522)Time elapsed: 0.117 s
% 0.22/0.53  % (15522)------------------------------
% 0.22/0.53  % (15522)------------------------------
% 0.22/0.53  % (15525)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (15524)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.54  % (15530)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (15527)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (15532)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (15533)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (15537)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.54  % (15538)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (15535)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (15517)Refutation not found, incomplete strategy% (15517)------------------------------
% 0.22/0.55  % (15517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15517)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15517)Memory used [KB]: 10618
% 0.22/0.55  % (15517)Time elapsed: 0.114 s
% 0.22/0.55  % (15517)------------------------------
% 0.22/0.55  % (15517)------------------------------
% 0.22/0.55  % (15518)Refutation not found, incomplete strategy% (15518)------------------------------
% 0.22/0.55  % (15518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15518)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15518)Memory used [KB]: 10746
% 0.22/0.55  % (15518)Time elapsed: 0.138 s
% 0.22/0.55  % (15518)------------------------------
% 0.22/0.55  % (15518)------------------------------
% 0.22/0.55  % (15529)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.58  % (15519)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f969,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f113,f118,f123,f128,f133,f138,f143,f148,f157,f159,f213,f237,f251,f276,f286,f291,f297,f314,f319,f343,f357,f383,f394,f401,f428,f494,f649,f863,f880,f951,f968])).
% 0.22/0.58  fof(f968,plain,(
% 0.22/0.58    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_53),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f963])).
% 0.22/0.58  fof(f963,plain,(
% 0.22/0.58    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_53)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f112,f117,f122,f127,f132,f541,f950,f147,f950,f77])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,axiom,(
% 0.22/0.58    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.22/0.58  fof(f147,plain,(
% 0.22/0.58    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl5_8),
% 0.22/0.58    inference(avatar_component_clause,[],[f145])).
% 0.22/0.58  fof(f145,plain,(
% 0.22/0.58    spl5_8 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.58  fof(f950,plain,(
% 0.22/0.58    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl5_53),
% 0.22/0.58    inference(avatar_component_clause,[],[f948])).
% 0.22/0.58  fof(f948,plain,(
% 0.22/0.58    spl5_53 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.22/0.58  fof(f541,plain,(
% 0.22/0.58    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f534])).
% 0.22/0.58  fof(f534,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.58    inference(superposition,[],[f99,f462])).
% 0.22/0.58  fof(f462,plain,(
% 0.22/0.58    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.22/0.58    inference(resolution,[],[f453,f176])).
% 0.22/0.58  fof(f176,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,sK4(k4_xboole_0(X0,X1)))) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.58    inference(resolution,[],[f103,f160])).
% 0.22/0.58  fof(f160,plain,(
% 0.22/0.58    ( ! [X0] : (~r1_tarski(X0,sK4(X0)) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(resolution,[],[f82,f102])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f57])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.58    inference(ennf_transformation,[],[f15])).
% 0.22/0.58  fof(f15,axiom,(
% 0.22/0.58    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.22/0.58  fof(f103,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f44])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.58  fof(f453,plain,(
% 0.22/0.58    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f449,f86])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.58  fof(f449,plain,(
% 0.22/0.58    ( ! [X4,X3] : (r1_tarski(k1_xboole_0,X4) | ~r1_tarski(X3,k2_xboole_0(X3,X4))) )),
% 0.22/0.58    inference(superposition,[],[f103,f414])).
% 0.22/0.58  fof(f414,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.58    inference(resolution,[],[f176,f86])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f63])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.58    inference(nnf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.58  fof(f132,plain,(
% 0.22/0.58    l1_orders_2(sK0) | ~spl5_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f130])).
% 0.22/0.58  fof(f130,plain,(
% 0.22/0.58    spl5_5 <=> l1_orders_2(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.58  fof(f127,plain,(
% 0.22/0.58    v5_orders_2(sK0) | ~spl5_4),
% 0.22/0.58    inference(avatar_component_clause,[],[f125])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    spl5_4 <=> v5_orders_2(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    v4_orders_2(sK0) | ~spl5_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f120])).
% 0.22/0.58  fof(f120,plain,(
% 0.22/0.58    spl5_3 <=> v4_orders_2(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    v3_orders_2(sK0) | ~spl5_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f115])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    spl5_2 <=> v3_orders_2(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.58  fof(f112,plain,(
% 0.22/0.58    ~v2_struct_0(sK0) | spl5_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f110])).
% 0.22/0.58  fof(f110,plain,(
% 0.22/0.58    spl5_1 <=> v2_struct_0(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.58  fof(f951,plain,(
% 0.22/0.58    spl5_53 | ~spl5_6 | ~spl5_25 | ~spl5_30 | ~spl5_33),
% 0.22/0.58    inference(avatar_split_clause,[],[f938,f426,f380,f316,f135,f948])).
% 0.22/0.58  fof(f135,plain,(
% 0.22/0.58    spl5_6 <=> m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.58  fof(f316,plain,(
% 0.22/0.58    spl5_25 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.22/0.58  fof(f380,plain,(
% 0.22/0.58    spl5_30 <=> m1_orders_2(sK2,sK0,sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.22/0.58  fof(f426,plain,(
% 0.22/0.58    spl5_33 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X1) | ~m1_orders_2(X1,sK0,X0) | ~r1_tarski(X0,u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.22/0.58  fof(f938,plain,(
% 0.22/0.58    m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl5_6 | ~spl5_25 | ~spl5_30 | ~spl5_33)),
% 0.22/0.58    inference(backward_demodulation,[],[f137,f936])).
% 0.22/0.58  fof(f936,plain,(
% 0.22/0.58    k1_xboole_0 = sK2 | (~spl5_25 | ~spl5_30 | ~spl5_33)),
% 0.22/0.58    inference(subsumption_resolution,[],[f932,f318])).
% 0.22/0.58  fof(f318,plain,(
% 0.22/0.58    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl5_25),
% 0.22/0.58    inference(avatar_component_clause,[],[f316])).
% 0.22/0.58  fof(f932,plain,(
% 0.22/0.58    k1_xboole_0 = sK2 | ~r1_tarski(sK2,u1_struct_0(sK0)) | (~spl5_30 | ~spl5_33)),
% 0.22/0.58    inference(subsumption_resolution,[],[f922,f382])).
% 0.22/0.58  fof(f382,plain,(
% 0.22/0.58    m1_orders_2(sK2,sK0,sK2) | ~spl5_30),
% 0.22/0.58    inference(avatar_component_clause,[],[f380])).
% 0.22/0.58  fof(f922,plain,(
% 0.22/0.58    ~m1_orders_2(sK2,sK0,sK2) | k1_xboole_0 = sK2 | ~r1_tarski(sK2,u1_struct_0(sK0)) | (~spl5_30 | ~spl5_33)),
% 0.22/0.58    inference(resolution,[],[f382,f427])).
% 0.22/0.58  fof(f427,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_orders_2(X1,sK0,X0) | ~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl5_33),
% 0.22/0.58    inference(avatar_component_clause,[],[f426])).
% 0.22/0.58  fof(f137,plain,(
% 0.22/0.58    m2_orders_2(sK2,sK0,sK1) | ~spl5_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f135])).
% 0.22/0.58  fof(f880,plain,(
% 0.22/0.58    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_21 | spl5_31 | ~spl5_52),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f873])).
% 0.22/0.58  fof(f873,plain,(
% 0.22/0.58    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_21 | spl5_31 | ~spl5_52)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f112,f117,f122,f127,f132,f393,f290,f862,f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X2,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,axiom,(
% 0.22/0.58    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.22/0.58  fof(f862,plain,(
% 0.22/0.58    m1_orders_2(sK3,sK0,sK2) | ~spl5_52),
% 0.22/0.58    inference(avatar_component_clause,[],[f860])).
% 0.22/0.58  fof(f860,plain,(
% 0.22/0.58    spl5_52 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.22/0.58  fof(f290,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_21),
% 0.22/0.58    inference(avatar_component_clause,[],[f288])).
% 0.22/0.58  fof(f288,plain,(
% 0.22/0.58    spl5_21 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.58  fof(f393,plain,(
% 0.22/0.58    ~r1_tarski(sK3,sK2) | spl5_31),
% 0.22/0.58    inference(avatar_component_clause,[],[f391])).
% 0.22/0.58  fof(f391,plain,(
% 0.22/0.58    spl5_31 <=> r1_tarski(sK3,sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.22/0.58  fof(f863,plain,(
% 0.22/0.58    spl5_52 | spl5_29 | ~spl5_7 | spl5_10 | ~spl5_43),
% 0.22/0.58    inference(avatar_split_clause,[],[f672,f647,f154,f140,f375,f860])).
% 0.22/0.58  fof(f375,plain,(
% 0.22/0.58    spl5_29 <=> sK2 = sK3),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    spl5_7 <=> m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.58  fof(f154,plain,(
% 0.22/0.58    spl5_10 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.58  fof(f647,plain,(
% 0.22/0.58    spl5_43 <=> ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.22/0.58  fof(f672,plain,(
% 0.22/0.58    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | (~spl5_7 | spl5_10 | ~spl5_43)),
% 0.22/0.58    inference(subsumption_resolution,[],[f670,f155])).
% 0.22/0.58  fof(f155,plain,(
% 0.22/0.58    ~m1_orders_2(sK2,sK0,sK3) | spl5_10),
% 0.22/0.58    inference(avatar_component_clause,[],[f154])).
% 0.22/0.58  fof(f670,plain,(
% 0.22/0.58    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3) | (~spl5_7 | ~spl5_43)),
% 0.22/0.58    inference(resolution,[],[f648,f142])).
% 0.22/0.58  fof(f142,plain,(
% 0.22/0.58    m2_orders_2(sK3,sK0,sK1) | ~spl5_7),
% 0.22/0.58    inference(avatar_component_clause,[],[f140])).
% 0.22/0.58  fof(f648,plain,(
% 0.22/0.58    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) ) | ~spl5_43),
% 0.22/0.58    inference(avatar_component_clause,[],[f647])).
% 0.22/0.58  fof(f649,plain,(
% 0.22/0.58    spl5_43 | ~spl5_6 | ~spl5_37),
% 0.22/0.58    inference(avatar_split_clause,[],[f497,f492,f135,f647])).
% 0.22/0.58  fof(f492,plain,(
% 0.22/0.58    spl5_37 <=> ! [X1,X0] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.22/0.58  fof(f497,plain,(
% 0.22/0.58    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) ) | (~spl5_6 | ~spl5_37)),
% 0.22/0.58    inference(resolution,[],[f493,f137])).
% 0.22/0.58  fof(f493,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | X0 = X1 | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl5_37),
% 0.22/0.58    inference(avatar_component_clause,[],[f492])).
% 0.22/0.58  fof(f494,plain,(
% 0.22/0.58    spl5_37 | ~spl5_8 | ~spl5_24),
% 0.22/0.58    inference(avatar_split_clause,[],[f323,f312,f145,f492])).
% 0.22/0.58  fof(f312,plain,(
% 0.22/0.58    spl5_24 <=> ! [X1,X0,X2] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.58  fof(f323,plain,(
% 0.22/0.58    ( ! [X0,X1] : (X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | (~spl5_8 | ~spl5_24)),
% 0.22/0.58    inference(resolution,[],[f313,f147])).
% 0.22/0.58  fof(f313,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) ) | ~spl5_24),
% 0.22/0.58    inference(avatar_component_clause,[],[f312])).
% 0.22/0.58  fof(f428,plain,(
% 0.22/0.58    spl5_33 | ~spl5_20),
% 0.22/0.58    inference(avatar_split_clause,[],[f292,f284,f426])).
% 0.22/0.58  fof(f284,plain,(
% 0.22/0.58    spl5_20 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.58  fof(f292,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X1) | ~m1_orders_2(X1,sK0,X0) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | ~spl5_20),
% 0.22/0.58    inference(resolution,[],[f285,f101])).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f64])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.58    inference(nnf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.58  fof(f285,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X1) | ~m1_orders_2(X1,sK0,X0)) ) | ~spl5_20),
% 0.22/0.58    inference(avatar_component_clause,[],[f284])).
% 0.22/0.58  fof(f401,plain,(
% 0.22/0.58    ~spl5_9 | ~spl5_29),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f400])).
% 0.22/0.58  fof(f400,plain,(
% 0.22/0.58    $false | (~spl5_9 | ~spl5_29)),
% 0.22/0.58    inference(subsumption_resolution,[],[f399,f85])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0] : ~r2_xboole_0(X0,X0)),
% 0.22/0.58    inference(rectify,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 0.22/0.58  fof(f399,plain,(
% 0.22/0.58    r2_xboole_0(sK2,sK2) | (~spl5_9 | ~spl5_29)),
% 0.22/0.58    inference(backward_demodulation,[],[f152,f377])).
% 0.22/0.58  fof(f377,plain,(
% 0.22/0.58    sK2 = sK3 | ~spl5_29),
% 0.22/0.58    inference(avatar_component_clause,[],[f375])).
% 0.22/0.58  fof(f152,plain,(
% 0.22/0.58    r2_xboole_0(sK2,sK3) | ~spl5_9),
% 0.22/0.58    inference(avatar_component_clause,[],[f150])).
% 0.22/0.58  fof(f150,plain,(
% 0.22/0.58    spl5_9 <=> r2_xboole_0(sK2,sK3)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.58  fof(f394,plain,(
% 0.22/0.58    ~spl5_31 | spl5_29 | ~spl5_9),
% 0.22/0.58    inference(avatar_split_clause,[],[f384,f150,f375,f391])).
% 0.22/0.58  fof(f384,plain,(
% 0.22/0.58    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl5_9),
% 0.22/0.58    inference(resolution,[],[f152,f166])).
% 0.22/0.58  fof(f166,plain,(
% 0.22/0.58    ( ! [X4,X3] : (~r2_xboole_0(X4,X3) | X3 = X4 | ~r1_tarski(X3,X4)) )),
% 0.22/0.58    inference(resolution,[],[f94,f95])).
% 0.22/0.58  fof(f95,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f62])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.58    inference(flattening,[],[f61])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.58    inference(nnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.58    inference(cnf_transformation,[],[f60])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(flattening,[],[f59])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.58    inference(nnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.58  fof(f383,plain,(
% 0.22/0.58    spl5_30 | spl5_9 | ~spl5_10 | ~spl5_27),
% 0.22/0.58    inference(avatar_split_clause,[],[f369,f354,f154,f150,f380])).
% 0.22/0.58  fof(f354,plain,(
% 0.22/0.58    spl5_27 <=> r1_tarski(sK2,sK3)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.58  fof(f369,plain,(
% 0.22/0.58    m1_orders_2(sK2,sK0,sK2) | (spl5_9 | ~spl5_10 | ~spl5_27)),
% 0.22/0.58    inference(backward_demodulation,[],[f156,f365])).
% 0.22/0.58  fof(f365,plain,(
% 0.22/0.58    sK2 = sK3 | (spl5_9 | ~spl5_27)),
% 0.22/0.58    inference(subsumption_resolution,[],[f363,f151])).
% 0.22/0.58  fof(f151,plain,(
% 0.22/0.58    ~r2_xboole_0(sK2,sK3) | spl5_9),
% 0.22/0.58    inference(avatar_component_clause,[],[f150])).
% 0.22/0.58  fof(f363,plain,(
% 0.22/0.58    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl5_27),
% 0.22/0.58    inference(resolution,[],[f356,f97])).
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f62])).
% 0.22/0.58  fof(f356,plain,(
% 0.22/0.58    r1_tarski(sK2,sK3) | ~spl5_27),
% 0.22/0.58    inference(avatar_component_clause,[],[f354])).
% 0.22/0.58  fof(f156,plain,(
% 0.22/0.58    m1_orders_2(sK2,sK0,sK3) | ~spl5_10),
% 0.22/0.58    inference(avatar_component_clause,[],[f154])).
% 0.22/0.58  fof(f357,plain,(
% 0.22/0.58    spl5_27 | ~spl5_10 | ~spl5_13 | ~spl5_26),
% 0.22/0.58    inference(avatar_split_clause,[],[f352,f340,f235,f154,f354])).
% 0.22/0.58  fof(f235,plain,(
% 0.22/0.58    spl5_13 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | r1_tarski(X0,X1) | ~r1_tarski(X1,u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.58  fof(f340,plain,(
% 0.22/0.58    spl5_26 <=> r1_tarski(sK3,u1_struct_0(sK0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.58  fof(f352,plain,(
% 0.22/0.58    r1_tarski(sK2,sK3) | (~spl5_10 | ~spl5_13 | ~spl5_26)),
% 0.22/0.58    inference(subsumption_resolution,[],[f351,f342])).
% 0.22/0.58  fof(f342,plain,(
% 0.22/0.58    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl5_26),
% 0.22/0.58    inference(avatar_component_clause,[],[f340])).
% 0.22/0.58  fof(f351,plain,(
% 0.22/0.58    r1_tarski(sK2,sK3) | ~r1_tarski(sK3,u1_struct_0(sK0)) | (~spl5_10 | ~spl5_13)),
% 0.22/0.58    inference(resolution,[],[f236,f156])).
% 0.22/0.58  fof(f236,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | r1_tarski(X0,X1) | ~r1_tarski(X1,u1_struct_0(sK0))) ) | ~spl5_13),
% 0.22/0.58    inference(avatar_component_clause,[],[f235])).
% 0.22/0.58  fof(f343,plain,(
% 0.22/0.58    spl5_26 | ~spl5_22),
% 0.22/0.58    inference(avatar_split_clause,[],[f327,f294,f340])).
% 0.22/0.58  fof(f294,plain,(
% 0.22/0.58    spl5_22 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.58  fof(f327,plain,(
% 0.22/0.58    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl5_22),
% 0.22/0.58    inference(resolution,[],[f296,f100])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f64])).
% 0.22/0.58  fof(f296,plain,(
% 0.22/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_22),
% 0.22/0.58    inference(avatar_component_clause,[],[f294])).
% 0.22/0.58  fof(f319,plain,(
% 0.22/0.58    spl5_25 | ~spl5_21),
% 0.22/0.58    inference(avatar_split_clause,[],[f305,f288,f316])).
% 0.22/0.58  fof(f305,plain,(
% 0.22/0.58    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl5_21),
% 0.22/0.58    inference(resolution,[],[f290,f100])).
% 0.22/0.58  fof(f314,plain,(
% 0.22/0.58    spl5_24 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f233,f130,f125,f120,f115,f110,f312])).
% 0.22/0.58  fof(f233,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f232,f112])).
% 0.22/0.58  fof(f232,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f231,f117])).
% 0.22/0.58  fof(f231,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f230,f122])).
% 1.74/0.60  fof(f230,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f229,f127])).
% 1.74/0.60  fof(f229,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 1.74/0.60    inference(resolution,[],[f79,f132])).
% 1.74/0.60  fof(f79,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X2,X0,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f56])).
% 1.74/0.60  fof(f56,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.74/0.60    inference(nnf_transformation,[],[f30])).
% 1.74/0.60  fof(f30,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.74/0.60    inference(flattening,[],[f29])).
% 1.74/0.60  fof(f29,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f21])).
% 1.74/0.60  fof(f21,axiom,(
% 1.74/0.60    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 1.74/0.60  fof(f297,plain,(
% 1.74/0.60    spl5_22 | ~spl5_7 | ~spl5_19),
% 1.74/0.60    inference(avatar_split_clause,[],[f282,f274,f140,f294])).
% 1.74/0.60  fof(f274,plain,(
% 1.74/0.60    spl5_19 <=> ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.74/0.60  fof(f282,plain,(
% 1.74/0.60    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_7 | ~spl5_19)),
% 1.74/0.60    inference(resolution,[],[f275,f142])).
% 1.74/0.60  fof(f275,plain,(
% 1.74/0.60    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_19),
% 1.74/0.60    inference(avatar_component_clause,[],[f274])).
% 1.74/0.60  fof(f291,plain,(
% 1.74/0.60    spl5_21 | ~spl5_6 | ~spl5_19),
% 1.74/0.60    inference(avatar_split_clause,[],[f281,f274,f135,f288])).
% 1.74/0.60  fof(f281,plain,(
% 1.74/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_6 | ~spl5_19)),
% 1.74/0.60    inference(resolution,[],[f275,f137])).
% 1.74/0.60  fof(f286,plain,(
% 1.74/0.60    spl5_20 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 1.74/0.60    inference(avatar_split_clause,[],[f218,f130,f125,f120,f115,f110,f284])).
% 1.74/0.60  fof(f218,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f217,f112])).
% 1.74/0.60  fof(f217,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f216,f117])).
% 1.74/0.60  fof(f216,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f215,f122])).
% 1.74/0.60  fof(f215,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f214,f127])).
% 1.74/0.60  fof(f214,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 1.74/0.60    inference(resolution,[],[f209,f132])).
% 1.74/0.60  fof(f209,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.74/0.60    inference(subsumption_resolution,[],[f81,f91])).
% 1.74/0.60  fof(f91,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f42])).
% 1.74/0.60  fof(f42,plain,(
% 1.74/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.74/0.60    inference(flattening,[],[f41])).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f16])).
% 1.74/0.60  fof(f16,axiom,(
% 1.74/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 1.74/0.60  fof(f81,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f34])).
% 1.74/0.60  fof(f34,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.74/0.60    inference(flattening,[],[f33])).
% 1.74/0.60  fof(f33,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f19])).
% 1.74/0.60  fof(f19,axiom,(
% 1.74/0.60    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 1.74/0.60  fof(f276,plain,(
% 1.74/0.60    spl5_19 | ~spl5_8 | ~spl5_15),
% 1.74/0.60    inference(avatar_split_clause,[],[f266,f249,f145,f274])).
% 1.74/0.60  fof(f249,plain,(
% 1.74/0.60    spl5_15 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.74/0.60  fof(f266,plain,(
% 1.74/0.60    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_8 | ~spl5_15)),
% 1.74/0.60    inference(resolution,[],[f250,f147])).
% 1.74/0.60  fof(f250,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_15),
% 1.74/0.60    inference(avatar_component_clause,[],[f249])).
% 1.74/0.60  fof(f251,plain,(
% 1.74/0.60    spl5_15 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 1.74/0.60    inference(avatar_split_clause,[],[f197,f130,f125,f120,f115,f110,f249])).
% 1.74/0.60  fof(f197,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f196,f112])).
% 1.74/0.60  fof(f196,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f195,f117])).
% 1.74/0.60  fof(f195,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f194,f122])).
% 1.74/0.60  fof(f194,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f193,f127])).
% 1.74/0.60  fof(f193,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 1.74/0.60    inference(resolution,[],[f90,f132])).
% 1.74/0.60  fof(f90,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f40])).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.74/0.60    inference(flattening,[],[f39])).
% 1.74/0.60  fof(f39,plain,(
% 1.74/0.60    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f17])).
% 1.74/0.60  fof(f17,axiom,(
% 1.74/0.60    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 1.74/0.60  fof(f237,plain,(
% 1.74/0.60    spl5_13 | ~spl5_11),
% 1.74/0.60    inference(avatar_split_clause,[],[f228,f211,f235])).
% 1.74/0.60  fof(f211,plain,(
% 1.74/0.60    spl5_11 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.74/0.60  fof(f228,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | r1_tarski(X0,X1) | ~r1_tarski(X1,u1_struct_0(sK0))) ) | ~spl5_11),
% 1.74/0.60    inference(resolution,[],[f212,f101])).
% 1.74/0.60  fof(f212,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,X1) | r1_tarski(X0,X1)) ) | ~spl5_11),
% 1.74/0.60    inference(avatar_component_clause,[],[f211])).
% 1.74/0.60  fof(f213,plain,(
% 1.74/0.60    spl5_11 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5),
% 1.74/0.60    inference(avatar_split_clause,[],[f186,f130,f125,f120,f115,f110,f211])).
% 1.74/0.60  fof(f186,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f185,f112])).
% 1.74/0.60  fof(f185,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f184,f117])).
% 1.74/0.60  fof(f184,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f183,f122])).
% 1.74/0.60  fof(f183,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f182,f127])).
% 1.74/0.60  fof(f182,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,X1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_5),
% 1.74/0.60    inference(resolution,[],[f80,f132])).
% 1.74/0.60  fof(f159,plain,(
% 1.74/0.60    ~spl5_9 | ~spl5_10),
% 1.74/0.60    inference(avatar_split_clause,[],[f158,f154,f150])).
% 1.74/0.60  fof(f158,plain,(
% 1.74/0.60    ~r2_xboole_0(sK2,sK3) | ~spl5_10),
% 1.74/0.60    inference(subsumption_resolution,[],[f74,f156])).
% 1.74/0.60  fof(f74,plain,(
% 1.74/0.60    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f55,plain,(
% 1.74/0.60    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.74/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f50,f54,f53,f52,f51])).
% 1.74/0.60  fof(f51,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f52,plain,(
% 1.74/0.60    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f53,plain,(
% 1.74/0.60    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f54,plain,(
% 1.74/0.60    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 1.74/0.60    introduced(choice_axiom,[])).
% 1.74/0.60  fof(f50,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.74/0.60    inference(flattening,[],[f49])).
% 1.74/0.60  fof(f49,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.74/0.60    inference(nnf_transformation,[],[f26])).
% 1.74/0.60  fof(f26,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.74/0.60    inference(flattening,[],[f25])).
% 1.74/0.60  fof(f25,plain,(
% 1.74/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f23])).
% 1.74/0.60  fof(f23,negated_conjecture,(
% 1.74/0.60    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.74/0.60    inference(negated_conjecture,[],[f22])).
% 1.74/0.60  fof(f22,conjecture,(
% 1.74/0.60    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.74/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 1.74/0.60  fof(f157,plain,(
% 1.74/0.60    spl5_9 | spl5_10),
% 1.74/0.60    inference(avatar_split_clause,[],[f73,f154,f150])).
% 1.74/0.60  fof(f73,plain,(
% 1.74/0.60    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f148,plain,(
% 1.74/0.60    spl5_8),
% 1.74/0.60    inference(avatar_split_clause,[],[f70,f145])).
% 1.74/0.60  fof(f70,plain,(
% 1.74/0.60    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f143,plain,(
% 1.74/0.60    spl5_7),
% 1.74/0.60    inference(avatar_split_clause,[],[f72,f140])).
% 1.74/0.60  fof(f72,plain,(
% 1.74/0.60    m2_orders_2(sK3,sK0,sK1)),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f138,plain,(
% 1.74/0.60    spl5_6),
% 1.74/0.60    inference(avatar_split_clause,[],[f71,f135])).
% 1.74/0.60  fof(f71,plain,(
% 1.74/0.60    m2_orders_2(sK2,sK0,sK1)),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f133,plain,(
% 1.74/0.60    spl5_5),
% 1.74/0.60    inference(avatar_split_clause,[],[f69,f130])).
% 1.74/0.60  fof(f69,plain,(
% 1.74/0.60    l1_orders_2(sK0)),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f128,plain,(
% 1.74/0.60    spl5_4),
% 1.74/0.60    inference(avatar_split_clause,[],[f68,f125])).
% 1.74/0.60  fof(f68,plain,(
% 1.74/0.60    v5_orders_2(sK0)),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f123,plain,(
% 1.74/0.60    spl5_3),
% 1.74/0.60    inference(avatar_split_clause,[],[f67,f120])).
% 1.74/0.60  fof(f67,plain,(
% 1.74/0.60    v4_orders_2(sK0)),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f118,plain,(
% 1.74/0.60    spl5_2),
% 1.74/0.60    inference(avatar_split_clause,[],[f66,f115])).
% 1.74/0.60  fof(f66,plain,(
% 1.74/0.60    v3_orders_2(sK0)),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f113,plain,(
% 1.74/0.60    ~spl5_1),
% 1.74/0.60    inference(avatar_split_clause,[],[f65,f110])).
% 1.74/0.60  fof(f65,plain,(
% 1.74/0.60    ~v2_struct_0(sK0)),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  % SZS output end Proof for theBenchmark
% 1.74/0.60  % (15519)------------------------------
% 1.74/0.60  % (15519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.60  % (15519)Termination reason: Refutation
% 1.74/0.60  
% 1.74/0.60  % (15519)Memory used [KB]: 6780
% 1.74/0.60  % (15519)Time elapsed: 0.156 s
% 1.74/0.60  % (15519)------------------------------
% 1.74/0.60  % (15519)------------------------------
% 1.74/0.61  % (15516)Success in time 0.243 s
%------------------------------------------------------------------------------
