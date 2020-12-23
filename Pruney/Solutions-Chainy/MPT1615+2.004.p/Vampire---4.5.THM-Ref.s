%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 133 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :    6
%              Number of atoms          :  244 ( 363 expanded)
%              Number of equality atoms :   61 (  89 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f66,f70,f78,f82,f96,f104,f108,f126,f133,f139,f150,f155,f161])).

fof(f161,plain,
    ( ~ spl2_13
    | ~ spl2_15
    | spl2_25 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl2_13
    | ~ spl2_15
    | spl2_25 ),
    inference(subsumption_resolution,[],[f158,f95])).

fof(f95,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl2_13
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f158,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl2_15
    | spl2_25 ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | ~ spl2_15
    | spl2_25 ),
    inference(superposition,[],[f154,f103])).

fof(f103,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_tarski(X0)
        | r2_hidden(sK1(X0),X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_15
  <=> ! [X0] :
        ( k1_xboole_0 = k3_tarski(X0)
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f154,plain,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | spl2_25 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl2_25
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f155,plain,
    ( ~ spl2_25
    | spl2_4
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f151,f148,f56,f153])).

fof(f56,plain,
    ( spl2_4
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f148,plain,
    ( spl2_24
  <=> k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f151,plain,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | spl2_4
    | ~ spl2_24 ),
    inference(superposition,[],[f57,f149])).

fof(f149,plain,
    ( k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f148])).

fof(f57,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f150,plain,
    ( spl2_24
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f142,f137,f106,f64,f148])).

fof(f64,plain,
    ( spl2_6
  <=> ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f106,plain,
    ( spl2_16
  <=> ! [X0] :
        ( ~ l1_orders_2(X0)
        | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f137,plain,
    ( spl2_22
  <=> k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f142,plain,
    ( k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f140,f65])).

fof(f65,plain,
    ( ! [X0] : l1_orders_2(k2_yellow_1(X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f140,plain,
    ( k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0)
    | ~ l1_orders_2(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(superposition,[],[f138,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
        | ~ l1_orders_2(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f138,plain,
    ( k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( spl2_22
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f134,f131,f68,f137])).

fof(f68,plain,
    ( spl2_7
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f131,plain,
    ( spl2_21
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
        | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f134,plain,
    ( k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0)
    | ~ spl2_7
    | ~ spl2_21 ),
    inference(resolution,[],[f132,f69])).

fof(f69,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
        | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( spl2_21
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f129,f124,f52,f48,f44,f131])).

fof(f44,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f48,plain,
    ( spl2_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f124,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(X0)))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
        | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f49,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
        | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) )
    | spl2_1
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f127,f45])).

fof(f45,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f127,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
        | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0) )
    | ~ spl2_3
    | ~ spl2_20 ),
    inference(resolution,[],[f125,f53])).

fof(f53,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(X0)))
        | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f124])).

fof(f126,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f42,f124])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(X0)))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) ) ),
    inference(forward_demodulation,[],[f34,f28])).

fof(f28,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
      | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
         => k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_1)).

fof(f108,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f33,f106])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f104,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f31,f102])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_tarski(X0)
      | r2_hidden(sK1(X0),X0) ) ),
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
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(f96,plain,
    ( spl2_13
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f91,f80,f76,f94])).

fof(f76,plain,
    ( spl2_9
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f80,plain,
    ( spl2_10
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f91,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(superposition,[],[f77,f81])).

fof(f81,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f77,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f82,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f78,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f35,f76])).

fof(f35,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f70,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f68])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f66,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f58,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

fof(f54,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (15791)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (15798)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (15791)Refutation not found, incomplete strategy% (15791)------------------------------
% 0.21/0.48  % (15791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15791)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (15791)Memory used [KB]: 6012
% 0.21/0.48  % (15791)Time elapsed: 0.003 s
% 0.21/0.48  % (15791)------------------------------
% 0.21/0.48  % (15791)------------------------------
% 0.21/0.51  % (15780)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (15783)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (15787)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (15787)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f46,f50,f54,f58,f66,f70,f78,f82,f96,f104,f108,f126,f133,f139,f150,f155,f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~spl2_13 | ~spl2_15 | spl2_25),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    $false | (~spl2_13 | ~spl2_15 | spl2_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f158,f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl2_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl2_13 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | (~spl2_15 | spl2_25)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f157])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | (~spl2_15 | spl2_25)),
% 0.21/0.52    inference(superposition,[],[f154,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_tarski(X0) | r2_hidden(sK1(X0),X0)) ) | ~spl2_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    spl2_15 <=> ! [X0] : (k1_xboole_0 = k3_tarski(X0) | r2_hidden(sK1(X0),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    k1_xboole_0 != k3_tarski(k1_xboole_0) | spl2_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl2_25 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~spl2_25 | spl2_4 | ~spl2_24),
% 0.21/0.52    inference(avatar_split_clause,[],[f151,f148,f56,f153])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    spl2_4 <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl2_24 <=> k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    k1_xboole_0 != k3_tarski(k1_xboole_0) | (spl2_4 | ~spl2_24)),
% 0.21/0.52    inference(superposition,[],[f57,f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0) | ~spl2_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f148])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f56])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl2_24 | ~spl2_6 | ~spl2_16 | ~spl2_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f142,f137,f106,f64,f148])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl2_6 <=> ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl2_16 <=> ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    spl2_22 <=> k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0) | (~spl2_6 | ~spl2_16 | ~spl2_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f140,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) ) | ~spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f64])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(k1_xboole_0) | ~l1_orders_2(k2_yellow_1(u1_pre_topc(sK0))) | (~spl2_16 | ~spl2_22)),
% 0.21/0.52    inference(superposition,[],[f138,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) ) | ~spl2_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0) | ~spl2_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f137])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl2_22 | ~spl2_7 | ~spl2_21),
% 0.21/0.52    inference(avatar_split_clause,[],[f134,f131,f68,f137])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl2_7 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl2_21 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    k3_tarski(k1_xboole_0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),k1_xboole_0) | (~spl2_7 | ~spl2_21)),
% 0.21/0.52    inference(resolution,[],[f132,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0)) ) | ~spl2_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    spl2_21 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f129,f124,f52,f48,f44,f131])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl2_1 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl2_2 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl2_3 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl2_20 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(X0))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0)) ) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f128,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f48])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0)) ) | (spl2_1 | ~spl2_3 | ~spl2_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f127,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f44])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | k3_tarski(X0) = k1_yellow_0(k2_yellow_1(u1_pre_topc(sK0)),X0)) ) | (~spl2_3 | ~spl2_20)),
% 0.21/0.52    inference(resolution,[],[f125,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f52])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(X0))) | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)) ) | ~spl2_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f124])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl2_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f124])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_pre_topc(X0))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f34,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) => k1_yellow_0(k2_yellow_1(u1_pre_topc(X0)),X1) = k3_tarski(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_1)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl2_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f106])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl2_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f31,f102])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_tarski(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.21/0.52    inference(rectify,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl2_13 | ~spl2_9 | ~spl2_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f91,f80,f76,f94])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl2_9 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl2_10 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl2_9 | ~spl2_10)),
% 0.21/0.52    inference(superposition,[],[f77,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl2_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl2_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl2_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f80])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl2_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f76])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl2_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f68])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl2_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f27,f64])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f56])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f52])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f48])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (15787)------------------------------
% 0.21/0.52  % (15787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15787)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (15787)Memory used [KB]: 10618
% 0.21/0.52  % (15787)Time elapsed: 0.078 s
% 0.21/0.52  % (15787)------------------------------
% 0.21/0.52  % (15787)------------------------------
% 0.21/0.52  % (15776)Success in time 0.164 s
%------------------------------------------------------------------------------
