%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 247 expanded)
%              Number of leaves         :   20 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  678 (1096 expanded)
%              Number of equality atoms :   38 (  67 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f73,f155,f159,f163,f170,f195,f216,f217])).

fof(f217,plain,
    ( k1_xboole_0 != sK4(k4_orders_2(sK0,sK1))
    | m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f216,plain,
    ( spl6_15
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f206,f193,f157,f214])).

fof(f214,plain,
    ( spl6_15
  <=> k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f157,plain,
    ( spl6_8
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f193,plain,
    ( spl6_13
  <=> r2_hidden(sK4(k4_orders_2(sK0,sK1)),k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f206,plain,
    ( k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f205,f158])).

fof(f158,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f205,plain,
    ( k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))
    | k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl6_13 ),
    inference(resolution,[],[f194,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 != k3_tarski(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(f194,plain,
    ( r2_hidden(sK4(k4_orders_2(sK0,sK1)),k4_orders_2(sK0,sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( spl6_13
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f171,f168,f71,f67,f63,f59,f55,f51,f193])).

fof(f51,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f55,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f59,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f63,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f67,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f71,plain,
    ( spl6_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f168,plain,
    ( spl6_10
  <=> m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f171,plain,
    ( r2_hidden(sK4(k4_orders_2(sK0,sK1)),k4_orders_2(sK0,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(resolution,[],[f169,f144])).

fof(f144,plain,
    ( ! [X10] :
        ( ~ m2_orders_2(X10,sK0,sK1)
        | r2_hidden(X10,k4_orders_2(sK0,sK1)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f143,f52])).

fof(f52,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f143,plain,
    ( ! [X10] :
        ( v2_struct_0(sK0)
        | ~ m2_orders_2(X10,sK0,sK1)
        | r2_hidden(X10,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f142,f68])).

fof(f68,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f142,plain,
    ( ! [X10] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X10,sK0,sK1)
        | r2_hidden(X10,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f141,f64])).

fof(f64,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f141,plain,
    ( ! [X10] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X10,sK0,sK1)
        | r2_hidden(X10,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f140,f60])).

fof(f60,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f140,plain,
    ( ! [X10] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X10,sK0,sK1)
        | r2_hidden(X10,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f84,f56])).

fof(f56,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f84,plain,
    ( ! [X10] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X10,sK0,sK1)
        | r2_hidden(X10,k4_orders_2(sK0,sK1)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

% (960)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(f72,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f169,plain,
    ( m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f168])).

fof(f170,plain,
    ( spl6_10
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f166,f153,f71,f67,f63,f59,f55,f51,f168])).

fof(f153,plain,
    ( spl6_7
  <=> v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f166,plain,
    ( m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(subsumption_resolution,[],[f165,f154])).

fof(f154,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f165,plain,
    ( m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)
    | v1_xboole_0(k4_orders_2(sK0,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f139,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f139,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k4_orders_2(sK0,sK1))
        | m2_orders_2(X9,sK0,sK1) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f138,f52])).

fof(f138,plain,
    ( ! [X9] :
        ( v2_struct_0(sK0)
        | m2_orders_2(X9,sK0,sK1)
        | ~ r2_hidden(X9,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f137,f68])).

fof(f137,plain,
    ( ! [X9] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | m2_orders_2(X9,sK0,sK1)
        | ~ r2_hidden(X9,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f136,f64])).

fof(f136,plain,
    ( ! [X9] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | m2_orders_2(X9,sK0,sK1)
        | ~ r2_hidden(X9,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f135,f60])).

fof(f135,plain,
    ( ! [X9] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | m2_orders_2(X9,sK0,sK1)
        | ~ r2_hidden(X9,k4_orders_2(sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f83,f56])).

fof(f83,plain,
    ( ! [X9] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | m2_orders_2(X9,sK0,sK1)
        | ~ r2_hidden(X9,k4_orders_2(sK0,sK1)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f163,plain,
    ( ~ spl6_9
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f151,f71,f67,f63,f59,f55,f51,f161])).

fof(f161,plain,
    ( spl6_9
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f151,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f150,f105])).

fof(f105,plain,
    ( ! [X2] :
        ( ~ m2_orders_2(X2,sK0,sK1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f104,f52])).

fof(f104,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f103,f68])).

fof(f103,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f102,f64])).

fof(f102,plain,
    ( ! [X2] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f101,f60])).

fof(f101,plain,
    ( ! [X2] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f77,f56])).

fof(f77,plain,
    ( ! [X2] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X2,sK0,sK1)
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f150,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f149,f100])).

fof(f100,plain,
    ( ! [X1] :
        ( ~ m2_orders_2(X1,sK0,sK1)
        | v6_orders_2(X1,sK0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f99,f52])).

fof(f99,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ m2_orders_2(X1,sK0,sK1)
        | v6_orders_2(X1,sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f98,f68])).

fof(f98,plain,
    ( ! [X1] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X1,sK0,sK1)
        | v6_orders_2(X1,sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f97,f64])).

fof(f97,plain,
    ( ! [X1] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X1,sK0,sK1)
        | v6_orders_2(X1,sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f96,f60])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X1,sK0,sK1)
        | v6_orders_2(X1,sK0) )
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f76,f56])).

fof(f76,plain,
    ( ! [X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m2_orders_2(X1,sK0,sK1)
        | v6_orders_2(X1,sK0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | v6_orders_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f149,plain,
    ( ~ v6_orders_2(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f148,f52])).

fof(f148,plain,
    ( v2_struct_0(sK0)
    | ~ v6_orders_2(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f147,f68])).

fof(f147,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v6_orders_2(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f146,f64])).

fof(f146,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v6_orders_2(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f145,f60])).

fof(f145,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v6_orders_2(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f85,f56])).

fof(f85,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v6_orders_2(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(k1_xboole_0,X0,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

fof(f159,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f24,f157])).

fof(f24,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(f155,plain,
    ( ~ spl6_7
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f95,f71,f67,f63,f59,f55,f51,f153])).

fof(f95,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f94,f52])).

fof(f94,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f93,f68])).

fof(f93,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f92,f64])).

fof(f92,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f91,f60])).

fof(f91,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f75,f56])).

fof(f75,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f73,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f23,f71])).

fof(f23,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:17:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (955)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (946)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (947)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (957)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (971)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (947)Refutation not found, incomplete strategy% (947)------------------------------
% 0.21/0.47  % (947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (947)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (947)Memory used [KB]: 10618
% 0.21/0.47  % (947)Time elapsed: 0.064 s
% 0.21/0.47  % (947)------------------------------
% 0.21/0.47  % (947)------------------------------
% 0.21/0.48  % (946)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f73,f155,f159,f163,f170,f195,f216,f217])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    k1_xboole_0 != sK4(k4_orders_2(sK0,sK1)) | m2_orders_2(k1_xboole_0,sK0,sK1) | ~m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    spl6_15 | ~spl6_8 | ~spl6_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f206,f193,f157,f214])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    spl6_15 <=> k1_xboole_0 = sK4(k4_orders_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl6_8 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    spl6_13 <=> r2_hidden(sK4(k4_orders_2(sK0,sK1)),k4_orders_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | (~spl6_8 | ~spl6_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f205,f158])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl6_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f157])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    k1_xboole_0 = sK4(k4_orders_2(sK0,sK1)) | k1_xboole_0 != k3_tarski(k4_orders_2(sK0,sK1)) | ~spl6_13),
% 0.21/0.48    inference(resolution,[],[f194,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2 | k1_xboole_0 != k3_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.21/0.48    inference(rectify,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    r2_hidden(sK4(k4_orders_2(sK0,sK1)),k4_orders_2(sK0,sK1)) | ~spl6_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f193])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    spl6_13 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f171,f168,f71,f67,f63,f59,f55,f51,f193])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl6_1 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl6_2 <=> v3_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl6_3 <=> v4_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl6_4 <=> v5_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl6_5 <=> l1_orders_2(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl6_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    spl6_10 <=> m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    r2_hidden(sK4(k4_orders_2(sK0,sK1)),k4_orders_2(sK0,sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_10)),
% 0.21/0.48    inference(resolution,[],[f169,f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X10] : (~m2_orders_2(X10,sK0,sK1) | r2_hidden(X10,k4_orders_2(sK0,sK1))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f143,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X10] : (v2_struct_0(sK0) | ~m2_orders_2(X10,sK0,sK1) | r2_hidden(X10,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f142,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    l1_orders_2(sK0) | ~spl6_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X10] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X10,sK0,sK1) | r2_hidden(X10,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f141,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v5_orders_2(sK0) | ~spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X10] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X10,sK0,sK1) | r2_hidden(X10,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    v4_orders_2(sK0) | ~spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ( ! [X10] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X10,sK0,sK1) | r2_hidden(X10,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    v3_orders_2(sK0) | ~spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X10] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X10,sK0,sK1) | r2_hidden(X10,k4_orders_2(sK0,sK1))) ) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f72,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  % (960)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl6_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) | ~spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f168])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    spl6_10 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f166,f153,f71,f67,f63,f59,f55,f51,f168])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    spl6_7 <=> v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f165,f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f153])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    m2_orders_2(sK4(k4_orders_2(sK0,sK1)),sK0,sK1) | v1_xboole_0(k4_orders_2(sK0,sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(resolution,[],[f139,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X9] : (~r2_hidden(X9,k4_orders_2(sK0,sK1)) | m2_orders_2(X9,sK0,sK1)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f52])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X9] : (v2_struct_0(sK0) | m2_orders_2(X9,sK0,sK1) | ~r2_hidden(X9,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f68])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X9] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(X9,sK0,sK1) | ~r2_hidden(X9,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f136,f64])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X9] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(X9,sK0,sK1) | ~r2_hidden(X9,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f60])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X9] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(X9,sK0,sK1) | ~r2_hidden(X9,k4_orders_2(sK0,sK1))) ) | (~spl6_2 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f56])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X9] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | m2_orders_2(X9,sK0,sK1) | ~r2_hidden(X9,k4_orders_2(sK0,sK1))) ) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f72,f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~spl6_9 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f151,f71,f67,f63,f59,f55,f51,f161])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl6_9 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~m2_orders_2(k1_xboole_0,sK0,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f150,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X2] : (~m2_orders_2(X2,sK0,sK1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f52])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ( ! [X2] : (v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f103,f68])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X2] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f64])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X2] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_2 | ~spl6_3 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f60])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X2] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_2 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f77,f56])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X2] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X2,sK0,sK1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f72,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X1] : (~m2_orders_2(X1,sK0,sK1) | v6_orders_2(X1,sK0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f52])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X1] : (v2_struct_0(sK0) | ~m2_orders_2(X1,sK0,sK1) | v6_orders_2(X1,sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f68])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X1] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X1,sK0,sK1) | v6_orders_2(X1,sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f97,f64])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X1,sK0,sK1) | v6_orders_2(X1,sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f60])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X1,sK0,sK1) | v6_orders_2(X1,sK0)) ) | (~spl6_2 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f56])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X1,sK0,sK1) | v6_orders_2(X1,sK0)) ) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f72,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~v6_orders_2(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f52])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f147,f68])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f146,f64])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_3 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f145,f60])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl6_2 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f56])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f72,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl6_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f157])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~spl6_7 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f95,f71,f67,f63,f59,f55,f51,f153])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f52])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f68])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f64])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f60])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (~spl6_2 | ~spl6_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f75,f56])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v1_xboole_0(k4_orders_2(sK0,sK1)) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f72,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~v1_xboole_0(k4_orders_2(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f71])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl6_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f67])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    l1_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f63])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v5_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f59])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v4_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f55])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    v3_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~spl6_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f51])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (946)------------------------------
% 0.21/0.48  % (946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (946)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (946)Memory used [KB]: 6268
% 0.21/0.49  % (946)Time elapsed: 0.070 s
% 0.21/0.49  % (946)------------------------------
% 0.21/0.49  % (946)------------------------------
% 0.21/0.49  % (945)Success in time 0.131 s
%------------------------------------------------------------------------------
