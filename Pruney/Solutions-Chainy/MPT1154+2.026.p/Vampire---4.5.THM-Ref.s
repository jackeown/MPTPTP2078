%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 222 expanded)
%              Number of leaves         :   30 ( 101 expanded)
%              Depth                    :    8
%              Number of atoms          :  394 ( 844 expanded)
%              Number of equality atoms :   29 (  49 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f73,f77,f83,f89,f93,f106,f109,f116,f121,f126,f132,f140,f148,f153,f156])).

fof(f156,plain,(
    spl2_19 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl2_19 ),
    inference(resolution,[],[f152,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f152,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK1))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl2_19
  <=> r1_tarski(k1_tarski(sK1),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f153,plain,
    ( ~ spl2_19
    | spl2_18 ),
    inference(avatar_split_clause,[],[f149,f146,f151])).

fof(f146,plain,
    ( spl2_18
  <=> r2_hidden(sK1,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f149,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tarski(sK1))
    | spl2_18 ),
    inference(resolution,[],[f147,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f147,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl2_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( ~ spl2_15
    | ~ spl2_18
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f143,f138,f130,f91,f146,f124])).

fof(f124,plain,
    ( spl2_15
  <=> r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f91,plain,
    ( spl2_10
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f130,plain,
    ( spl2_16
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f138,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,k1_orders_2(sK0,X1))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f143,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl2_10
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(resolution,[],[f141,f131])).

fof(f131,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f130])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(sK1,X0)
        | ~ r2_hidden(sK1,k1_orders_2(sK0,X0)) )
    | ~ spl2_10
    | ~ spl2_17 ),
    inference(resolution,[],[f139,f92])).

fof(f92,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,k1_orders_2(sK0,X1))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl2_7
    | ~ spl2_6
    | ~ spl2_5
    | ~ spl2_3
    | spl2_17
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f135,f81,f63,f138,f59,f67,f71,f75])).

fof(f75,plain,
    ( spl2_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f71,plain,
    ( spl2_6
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f67,plain,
    ( spl2_5
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f59,plain,
    ( spl2_3
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f63,plain,
    ( spl2_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f81,plain,
    ( spl2_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(X0,k1_orders_2(sK0,X1))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f134,f82])).

fof(f82,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(X0,k1_orders_2(sK0,X1))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f133,f82])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(X0,k1_orders_2(sK0,X1))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f39,f64])).

fof(f64,plain,
    ( v5_orders_2(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_hidden(X1,k1_orders_2(X0,X2))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

fof(f132,plain,
    ( ~ spl2_10
    | spl2_16
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f127,f119,f114,f130,f91])).

fof(f114,plain,
    ( spl2_13
  <=> ! [X0] :
        ( m1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f119,plain,
    ( spl2_14
  <=> k6_domain_1(k2_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f127,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(superposition,[],[f115,f120])).

fof(f120,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f115,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f126,plain,
    ( spl2_15
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f122,f119,f87,f124])).

fof(f87,plain,
    ( spl2_9
  <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f122,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(superposition,[],[f88,f120])).

fof(f88,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f121,plain,
    ( spl2_14
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f117,f104,f91,f119])).

fof(f104,plain,
    ( spl2_12
  <=> ! [X0] :
        ( k1_tarski(X0) = k6_domain_1(k2_struct_0(sK0),X0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f117,plain,
    ( k6_domain_1(k2_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(resolution,[],[f105,f92])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_struct_0(sK0))
        | k1_tarski(X0) = k6_domain_1(k2_struct_0(sK0),X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f116,plain,
    ( spl2_7
    | ~ spl2_6
    | ~ spl2_3
    | spl2_13
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f110,f81,f114,f59,f71,f75])).

fof(f110,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k2_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl2_8 ),
    inference(superposition,[],[f40,f82])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

% (517)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f109,plain,
    ( ~ spl2_3
    | spl2_11 ),
    inference(avatar_split_clause,[],[f107,f101,f59])).

fof(f101,plain,
    ( spl2_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f107,plain,
    ( ~ l1_orders_2(sK0)
    | spl2_11 ),
    inference(resolution,[],[f102,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f102,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f106,plain,
    ( ~ spl2_11
    | spl2_12
    | spl2_7 ),
    inference(avatar_split_clause,[],[f99,f75,f104,f101])).

fof(f99,plain,
    ( ! [X0] :
        ( k1_tarski(X0) = k6_domain_1(k2_struct_0(sK0),X0)
        | ~ l1_struct_0(sK0)
        | ~ m1_subset_1(X0,k2_struct_0(sK0)) )
    | spl2_7 ),
    inference(resolution,[],[f94,f76])).

fof(f76,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | k1_tarski(X0) = k6_domain_1(k2_struct_0(X1),X0)
      | ~ l1_struct_0(X1)
      | ~ m1_subset_1(X0,k2_struct_0(X1)) ) ),
    inference(resolution,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f93,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f85,f81,f55,f91])).

fof(f55,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(superposition,[],[f56,f82])).

fof(f56,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f89,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f84,f81,f51,f87])).

fof(f51,plain,
    ( spl2_1
  <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f84,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(superposition,[],[f52,f82])).

fof(f52,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f83,plain,
    ( spl2_8
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f79,f59,f81])).

fof(f79,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f78,f60])).

fof(f60,plain,
    ( l1_orders_2(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f37,f38])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f77,plain,(
    ~ spl2_7 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

fof(f73,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f32,f67])).

fof(f32,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f34,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f35,f55])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f36,f51])).

fof(f36,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (515)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (499)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (518)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (504)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (509)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (504)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f73,f77,f83,f89,f93,f106,f109,f116,f121,f126,f132,f140,f148,f153,f156])).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    spl2_19),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    $false | spl2_19),
% 0.20/0.49    inference(resolution,[],[f152,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    ~r1_tarski(k1_tarski(sK1),k1_tarski(sK1)) | spl2_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    spl2_19 <=> r1_tarski(k1_tarski(sK1),k1_tarski(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ~spl2_19 | spl2_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f149,f146,f151])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    spl2_18 <=> r2_hidden(sK1,k1_tarski(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ~r1_tarski(k1_tarski(sK1),k1_tarski(sK1)) | spl2_18),
% 0.20/0.49    inference(resolution,[],[f147,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k1_tarski(sK1)) | spl2_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f146])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ~spl2_15 | ~spl2_18 | ~spl2_10 | ~spl2_16 | ~spl2_17),
% 0.20/0.49    inference(avatar_split_clause,[],[f143,f138,f130,f91,f146,f124])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    spl2_15 <=> r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl2_10 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    spl2_16 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    spl2_17 <=> ! [X1,X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k1_orders_2(sK0,X1)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) | (~spl2_10 | ~spl2_16 | ~spl2_17)),
% 0.20/0.49    inference(resolution,[],[f141,f131])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f130])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~r2_hidden(sK1,k1_orders_2(sK0,X0))) ) | (~spl2_10 | ~spl2_17)),
% 0.20/0.49    inference(resolution,[],[f139,f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl2_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f91])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,k1_orders_2(sK0,X1)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl2_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f138])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    spl2_7 | ~spl2_6 | ~spl2_5 | ~spl2_3 | spl2_17 | ~spl2_4 | ~spl2_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f135,f81,f63,f138,f59,f67,f71,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl2_7 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    spl2_6 <=> v3_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl2_5 <=> v4_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl2_3 <=> l1_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl2_4 <=> v5_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl2_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~l1_orders_2(sK0) | ~r2_hidden(X0,k1_orders_2(sK0,X1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl2_4 | ~spl2_8)),
% 0.20/0.49    inference(forward_demodulation,[],[f134,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_hidden(X0,k1_orders_2(sK0,X1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl2_4 | ~spl2_8)),
% 0.20/0.49    inference(forward_demodulation,[],[f133,f82])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_hidden(X0,k1_orders_2(sK0,X1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl2_4),
% 0.20/0.49    inference(resolution,[],[f39,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    v5_orders_2(sK0) | ~spl2_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f63])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_hidden(X1,k1_orders_2(X0,X2)) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ~spl2_10 | spl2_16 | ~spl2_13 | ~spl2_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f127,f119,f114,f130,f91])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl2_13 <=> ! [X0] : (m1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    spl2_14 <=> k6_domain_1(k2_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl2_13 | ~spl2_14)),
% 0.20/0.49    inference(superposition,[],[f115,f120])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    k6_domain_1(k2_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl2_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f119])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | ~spl2_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    spl2_15 | ~spl2_9 | ~spl2_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f122,f119,f87,f124])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl2_9 <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k2_struct_0(sK0),sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) | (~spl2_9 | ~spl2_14)),
% 0.20/0.49    inference(superposition,[],[f88,f120])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k2_struct_0(sK0),sK1))) | ~spl2_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f87])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl2_14 | ~spl2_10 | ~spl2_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f117,f104,f91,f119])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    spl2_12 <=> ! [X0] : (k1_tarski(X0) = k6_domain_1(k2_struct_0(sK0),X0) | ~m1_subset_1(X0,k2_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    k6_domain_1(k2_struct_0(sK0),sK1) = k1_tarski(sK1) | (~spl2_10 | ~spl2_12)),
% 0.20/0.49    inference(resolution,[],[f105,f92])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | k1_tarski(X0) = k6_domain_1(k2_struct_0(sK0),X0)) ) | ~spl2_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f104])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl2_7 | ~spl2_6 | ~spl2_3 | spl2_13 | ~spl2_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f110,f81,f114,f59,f71,f75])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k2_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl2_8),
% 0.20/0.49    inference(superposition,[],[f40,f82])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  % (517)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ~spl2_3 | spl2_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f107,f101,f59])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl2_11 <=> l1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ~l1_orders_2(sK0) | spl2_11),
% 0.20/0.49    inference(resolution,[],[f102,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ~l1_struct_0(sK0) | spl2_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ~spl2_11 | spl2_12 | spl2_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f99,f75,f104,f101])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k6_domain_1(k2_struct_0(sK0),X0) | ~l1_struct_0(sK0) | ~m1_subset_1(X0,k2_struct_0(sK0))) ) | spl2_7),
% 0.20/0.49    inference(resolution,[],[f94,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~v2_struct_0(sK0) | spl2_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X1) | k1_tarski(X0) = k6_domain_1(k2_struct_0(X1),X0) | ~l1_struct_0(X1) | ~m1_subset_1(X0,k2_struct_0(X1))) )),
% 0.20/0.49    inference(resolution,[],[f42,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k1_tarski(X1) = k6_domain_1(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl2_10 | ~spl2_2 | ~spl2_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f85,f81,f55,f91])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl2_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl2_2 | ~spl2_8)),
% 0.20/0.49    inference(superposition,[],[f56,f82])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl2_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f55])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl2_9 | ~spl2_1 | ~spl2_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f84,f81,f51,f87])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    spl2_1 <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k2_struct_0(sK0),sK1))) | (~spl2_1 | ~spl2_8)),
% 0.20/0.49    inference(superposition,[],[f52,f82])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~spl2_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f51])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl2_8 | ~spl2_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f79,f59,f81])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_3),
% 0.20/0.49    inference(resolution,[],[f78,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    l1_orders_2(sK0) | ~spl2_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f59])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_orders_2(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f37,f38])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ~spl2_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f75])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    (r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f25,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ? [X1] : (r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) => (r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    spl2_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f71])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    v3_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl2_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f67])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    v4_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl2_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f63])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    v5_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl2_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f34,f59])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    l1_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f35,f55])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl2_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f36,f51])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (504)------------------------------
% 0.20/0.49  % (504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (504)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (504)Memory used [KB]: 10746
% 0.20/0.49  % (504)Time elapsed: 0.009 s
% 0.20/0.49  % (504)------------------------------
% 0.20/0.49  % (504)------------------------------
% 0.20/0.49  % (513)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (510)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (513)Refutation not found, incomplete strategy% (513)------------------------------
% 0.20/0.50  % (513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (497)Success in time 0.137 s
%------------------------------------------------------------------------------
