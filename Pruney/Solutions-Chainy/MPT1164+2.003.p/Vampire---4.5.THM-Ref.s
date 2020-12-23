%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 404 expanded)
%              Number of leaves         :   26 ( 163 expanded)
%              Depth                    :   15
%              Number of atoms          :  861 (1821 expanded)
%              Number of equality atoms :   58 ( 118 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f665,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f109,f115,f120,f133,f142,f168,f184,f190,f210,f250,f263,f303,f365,f411,f493,f662])).

fof(f662,plain,
    ( spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f661])).

fof(f661,plain,
    ( $false
    | spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f658,f108])).

fof(f108,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_6
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f658,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_22 ),
    inference(resolution,[],[f265,f132])).

fof(f132,plain,
    ( r2_hidden(sK4(sK2,sK1),sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl5_10
  <=> r2_hidden(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,sK1),sK2)
        | r1_tarski(X0,sK1) )
    | ~ spl5_11
    | ~ spl5_22 ),
    inference(resolution,[],[f264,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f264,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl5_11
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f249,f147])).

fof(f147,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl5_11 ),
    inference(resolution,[],[f141,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f141,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f249,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl5_22
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f493,plain,
    ( spl5_29
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f447,f300,f187,f70,f65,f60,f55,f50,f367])).

fof(f367,plain,
    ( spl5_29
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f50,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f55,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f60,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f65,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f70,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f187,plain,
    ( spl5_16
  <=> m1_orders_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f300,plain,
    ( spl5_25
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f447,plain,
    ( k1_xboole_0 = sK2
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16
    | ~ spl5_25 ),
    inference(resolution,[],[f419,f189])).

fof(f189,plain,
    ( m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f419,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,k1_xboole_0)
        | k1_xboole_0 = X2 )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f319,f305])).

fof(f305,plain,
    ( ! [X1] :
        ( ~ m1_orders_2(X1,sK0,k1_xboole_0)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(resolution,[],[f302,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f82,f52])).

fof(f52,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f81,f67])).

fof(f67,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f80,f62])).

fof(f62,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f74,f57])).

fof(f57,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,X0)
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f72,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f302,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f300])).

fof(f319,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ m1_orders_2(X2,sK0,k1_xboole_0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f318,f52])).

fof(f318,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ m1_orders_2(X2,sK0,k1_xboole_0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f317,f72])).

fof(f317,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ m1_orders_2(X2,sK0,k1_xboole_0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f316,f67])).

fof(f316,plain,
    ( ! [X2] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ m1_orders_2(X2,sK0,k1_xboole_0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f315,f62])).

fof(f315,plain,
    ( ! [X2] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ m1_orders_2(X2,sK0,k1_xboole_0) )
    | ~ spl5_2
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f307,f57])).

fof(f307,plain,
    ( ! [X2] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ m1_orders_2(X2,sK0,k1_xboole_0) )
    | ~ spl5_25 ),
    inference(resolution,[],[f302,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

fof(f411,plain,
    ( spl5_15
    | ~ spl5_28
    | ~ spl5_29 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | spl5_15
    | ~ spl5_28
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f371,f386])).

fof(f386,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl5_15
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f183,f369])).

fof(f369,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f367])).

fof(f183,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl5_15
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f371,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_28 ),
    inference(resolution,[],[f364,f40])).

fof(f364,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl5_28
  <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f365,plain,
    ( spl5_28
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f339,f300,f207,f187,f165,f117,f70,f65,f60,f55,f50,f362])).

fof(f117,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f165,plain,
    ( spl5_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f207,plain,
    ( spl5_18
  <=> r2_hidden(sK4(sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f339,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_25 ),
    inference(backward_demodulation,[],[f209,f331])).

fof(f331,plain,
    ( k1_xboole_0 = sK2
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_16
    | ~ spl5_25 ),
    inference(resolution,[],[f320,f189])).

fof(f320,plain,
    ( ! [X2] :
        ( ~ m1_orders_2(X2,sK0,k1_xboole_0)
        | k1_xboole_0 = X2 )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f319,f287])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,k1_xboole_0)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f136,f167])).

fof(f167,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f83,f119])).

fof(f119,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f209,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0),sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f207])).

fof(f303,plain,
    ( spl5_25
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f171,f165,f117,f300])).

fof(f171,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f119,f167])).

fof(f263,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11
    | spl5_14
    | spl5_21 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11
    | spl5_14
    | spl5_21 ),
    inference(subsumption_resolution,[],[f261,f114])).

fof(f114,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_7
  <=> m1_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f261,plain,
    ( ~ m1_orders_2(sK2,sK0,sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_11
    | spl5_14
    | spl5_21 ),
    inference(subsumption_resolution,[],[f260,f52])).

fof(f260,plain,
    ( v2_struct_0(sK0)
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_11
    | spl5_14
    | spl5_21 ),
    inference(subsumption_resolution,[],[f259,f166])).

fof(f166,plain,
    ( k1_xboole_0 != sK1
    | spl5_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f259,plain,
    ( k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_11
    | spl5_21 ),
    inference(subsumption_resolution,[],[f258,f141])).

fof(f258,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | spl5_21 ),
    inference(subsumption_resolution,[],[f257,f119])).

fof(f257,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | spl5_21 ),
    inference(subsumption_resolution,[],[f256,f72])).

fof(f256,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_21 ),
    inference(subsumption_resolution,[],[f255,f67])).

fof(f255,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_21 ),
    inference(subsumption_resolution,[],[f254,f62])).

fof(f254,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK2,sK0,sK1)
    | ~ spl5_2
    | spl5_21 ),
    inference(subsumption_resolution,[],[f251,f57])).

fof(f251,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0)
    | ~ m1_orders_2(sK2,sK0,sK1)
    | spl5_21 ),
    inference(resolution,[],[f246,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | v2_struct_0(X0)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f246,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl5_21
  <=> m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f250,plain,
    ( ~ spl5_21
    | spl5_22
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f232,f161,f117,f70,f65,f60,f55,f50,f248,f244])).

fof(f161,plain,
    ( spl5_13
  <=> sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f232,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f229,f119])).

% (19054)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (19046)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f229,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_13 ),
    inference(superposition,[],[f99,f163])).

fof(f163,plain,
    ( sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f99,plain,
    ( ! [X10,X11,X9] :
        ( ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X9,X11)
        | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f98,f52])).

fof(f98,plain,
    ( ! [X10,X11,X9] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X9,X11)
        | ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f97,f67])).

fof(f97,plain,
    ( ! [X10,X11,X9] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X9,X11)
        | ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10)) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f96,f62])).

fof(f96,plain,
    ( ! [X10,X11,X9] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X9,X11)
        | ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10)) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f78,f57])).

fof(f78,plain,
    ( ! [X10,X11,X9] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X9,X11)
        | ~ r2_hidden(X9,k3_orders_2(sK0,X11,X10)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f210,plain,
    ( spl5_18
    | spl5_15 ),
    inference(avatar_split_clause,[],[f185,f181,f207])).

fof(f185,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0),sK2)
    | spl5_15 ),
    inference(resolution,[],[f183,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f190,plain,
    ( spl5_16
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f170,f165,f112,f187])).

fof(f170,plain,
    ( m1_orders_2(sK2,sK0,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f114,f167])).

fof(f184,plain,
    ( ~ spl5_15
    | spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f169,f165,f106,f181])).

fof(f169,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl5_6
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f108,f167])).

fof(f168,plain,
    ( spl5_13
    | spl5_14
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f157,f139,f117,f112,f70,f65,f60,f55,f50,f165,f161])).

fof(f157,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f156,f119])).

fof(f156,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f155,f141])).

fof(f155,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f91,f114])).

fof(f91,plain,
    ( ! [X4,X5] :
        ( ~ m1_orders_2(X5,sK0,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f90,f52])).

fof(f90,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_orders_2(X5,sK0,X4) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f89,f67])).

fof(f89,plain,
    ( ! [X4,X5] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_orders_2(X5,sK0,X4) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f88,f62])).

fof(f88,plain,
    ( ! [X4,X5] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_orders_2(X5,sK0,X4) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f76,f57])).

fof(f76,plain,
    ( ! [X4,X5] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X4
        | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5
        | ~ m1_orders_2(X5,sK0,X4) )
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f142,plain,
    ( spl5_11
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f137,f117,f112,f70,f65,f60,f55,f50,f139])).

fof(f137,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(resolution,[],[f136,f114])).

fof(f133,plain,
    ( spl5_10
    | spl5_6 ),
    inference(avatar_split_clause,[],[f110,f106,f130])).

fof(f110,plain,
    ( r2_hidden(sK4(sK2,sK1),sK2)
    | spl5_6 ),
    inference(resolution,[],[f108,f39])).

fof(f120,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f22,f117])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_orders_2(X2,X0,X1)
               => r1_tarski(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f115,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f20,f112])).

fof(f20,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f109,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f21,f106])).

fof(f21,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f27,f70])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:32:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (19053)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (19041)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (19045)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (19061)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (19048)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (19049)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (19035)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (19058)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (19036)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (19050)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (19039)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (19059)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (19040)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (19039)Refutation not found, incomplete strategy% (19039)------------------------------
% 0.21/0.54  % (19039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19039)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (19039)Memory used [KB]: 6140
% 0.21/0.54  % (19039)Time elapsed: 0.124 s
% 0.21/0.54  % (19039)------------------------------
% 0.21/0.54  % (19039)------------------------------
% 0.21/0.54  % (19057)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (19037)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (19057)Refutation not found, incomplete strategy% (19057)------------------------------
% 0.21/0.55  % (19057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19057)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19057)Memory used [KB]: 10746
% 0.21/0.55  % (19057)Time elapsed: 0.129 s
% 0.21/0.55  % (19057)------------------------------
% 0.21/0.55  % (19057)------------------------------
% 0.21/0.55  % (19063)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (19062)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (19055)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (19047)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (19052)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (19042)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (19044)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (19043)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (19051)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (19064)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (19056)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (19060)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (19038)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (19055)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f665,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f109,f115,f120,f133,f142,f168,f184,f190,f210,f250,f263,f303,f365,f411,f493,f662])).
% 0.21/0.58  fof(f662,plain,(
% 0.21/0.58    spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_22),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f661])).
% 0.21/0.58  fof(f661,plain,(
% 0.21/0.58    $false | (spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_22)),
% 0.21/0.58    inference(subsumption_resolution,[],[f658,f108])).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    ~r1_tarski(sK2,sK1) | spl5_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f106])).
% 0.21/0.58  fof(f106,plain,(
% 0.21/0.58    spl5_6 <=> r1_tarski(sK2,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.58  fof(f658,plain,(
% 0.21/0.58    r1_tarski(sK2,sK1) | (~spl5_10 | ~spl5_11 | ~spl5_22)),
% 0.21/0.58    inference(resolution,[],[f265,f132])).
% 0.21/0.58  fof(f132,plain,(
% 0.21/0.58    r2_hidden(sK4(sK2,sK1),sK2) | ~spl5_10),
% 0.21/0.58    inference(avatar_component_clause,[],[f130])).
% 0.21/0.58  fof(f130,plain,(
% 0.21/0.58    spl5_10 <=> r2_hidden(sK4(sK2,sK1),sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.58  fof(f265,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),sK2) | r1_tarski(X0,sK1)) ) | (~spl5_11 | ~spl5_22)),
% 0.21/0.58    inference(resolution,[],[f264,f40])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.58  fof(f264,plain,(
% 0.21/0.58    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,sK2)) ) | (~spl5_11 | ~spl5_22)),
% 0.21/0.58    inference(subsumption_resolution,[],[f249,f147])).
% 0.21/0.58  fof(f147,plain,(
% 0.21/0.58    ( ! [X2] : (m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK2)) ) | ~spl5_11),
% 0.21/0.58    inference(resolution,[],[f141,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.58    inference(flattening,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.58    inference(ennf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.58  fof(f141,plain,(
% 0.21/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f139])).
% 0.21/0.58  fof(f139,plain,(
% 0.21/0.58    spl5_11 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.58  fof(f249,plain,(
% 0.21/0.58    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1)) ) | ~spl5_22),
% 0.21/0.58    inference(avatar_component_clause,[],[f248])).
% 0.21/0.58  fof(f248,plain,(
% 0.21/0.58    spl5_22 <=> ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.58  fof(f493,plain,(
% 0.21/0.58    spl5_29 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_16 | ~spl5_25),
% 0.21/0.58    inference(avatar_split_clause,[],[f447,f300,f187,f70,f65,f60,f55,f50,f367])).
% 0.21/0.58  fof(f367,plain,(
% 0.21/0.58    spl5_29 <=> k1_xboole_0 = sK2),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    spl5_2 <=> v3_orders_2(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    spl5_3 <=> v4_orders_2(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    spl5_4 <=> v5_orders_2(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    spl5_5 <=> l1_orders_2(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.58  fof(f187,plain,(
% 0.21/0.58    spl5_16 <=> m1_orders_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.58  fof(f300,plain,(
% 0.21/0.58    spl5_25 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.58  fof(f447,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_16 | ~spl5_25)),
% 0.21/0.58    inference(resolution,[],[f419,f189])).
% 0.21/0.58  fof(f189,plain,(
% 0.21/0.58    m1_orders_2(sK2,sK0,k1_xboole_0) | ~spl5_16),
% 0.21/0.58    inference(avatar_component_clause,[],[f187])).
% 0.21/0.58  fof(f419,plain,(
% 0.21/0.58    ( ! [X2] : (~m1_orders_2(X2,sK0,k1_xboole_0) | k1_xboole_0 = X2) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_25)),
% 0.21/0.58    inference(subsumption_resolution,[],[f319,f305])).
% 0.21/0.58  fof(f305,plain,(
% 0.21/0.58    ( ! [X1] : (~m1_orders_2(X1,sK0,k1_xboole_0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_25)),
% 0.21/0.58    inference(resolution,[],[f302,f83])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f82,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f50])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f81,f67])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    v5_orders_2(sK0) | ~spl5_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f65])).
% 0.21/0.58  fof(f81,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f80,f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    v4_orders_2(sK0) | ~spl5_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f60])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_5)),
% 0.21/0.58    inference(subsumption_resolution,[],[f74,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    v3_orders_2(sK0) | ~spl5_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f55])).
% 0.21/0.58  fof(f74,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_5),
% 0.21/0.58    inference(resolution,[],[f72,f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f15])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.21/0.58  fof(f72,plain,(
% 0.21/0.58    l1_orders_2(sK0) | ~spl5_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f70])).
% 0.21/0.58  fof(f302,plain,(
% 0.21/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_25),
% 0.21/0.58    inference(avatar_component_clause,[],[f300])).
% 0.21/0.58  fof(f319,plain,(
% 0.21/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,sK0,k1_xboole_0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_25)),
% 0.21/0.58    inference(subsumption_resolution,[],[f318,f52])).
% 0.21/0.58  fof(f318,plain,(
% 0.21/0.58    ( ! [X2] : (v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,sK0,k1_xboole_0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_25)),
% 0.21/0.58    inference(subsumption_resolution,[],[f317,f72])).
% 0.21/0.58  fof(f317,plain,(
% 0.21/0.58    ( ! [X2] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,sK0,k1_xboole_0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_25)),
% 0.21/0.58    inference(subsumption_resolution,[],[f316,f67])).
% 0.21/0.58  fof(f316,plain,(
% 0.21/0.58    ( ! [X2] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,sK0,k1_xboole_0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_25)),
% 0.21/0.58    inference(subsumption_resolution,[],[f315,f62])).
% 0.21/0.58  fof(f315,plain,(
% 0.21/0.58    ( ! [X2] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,sK0,k1_xboole_0)) ) | (~spl5_2 | ~spl5_25)),
% 0.21/0.58    inference(subsumption_resolution,[],[f307,f57])).
% 0.21/0.58  fof(f307,plain,(
% 0.21/0.58    ( ! [X2] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,sK0,k1_xboole_0)) ) | ~spl5_25),
% 0.21/0.58    inference(resolution,[],[f302,f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X2,X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.58    inference(equality_resolution,[],[f36])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f13])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).
% 0.21/0.58  fof(f411,plain,(
% 0.21/0.58    spl5_15 | ~spl5_28 | ~spl5_29),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f410])).
% 0.21/0.58  fof(f410,plain,(
% 0.21/0.58    $false | (spl5_15 | ~spl5_28 | ~spl5_29)),
% 0.21/0.58    inference(subsumption_resolution,[],[f371,f386])).
% 0.21/0.58  fof(f386,plain,(
% 0.21/0.58    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (spl5_15 | ~spl5_29)),
% 0.21/0.58    inference(forward_demodulation,[],[f183,f369])).
% 0.21/0.58  fof(f369,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | ~spl5_29),
% 0.21/0.58    inference(avatar_component_clause,[],[f367])).
% 0.21/0.58  fof(f183,plain,(
% 0.21/0.58    ~r1_tarski(sK2,k1_xboole_0) | spl5_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f181])).
% 0.21/0.58  fof(f181,plain,(
% 0.21/0.58    spl5_15 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.58  fof(f371,plain,(
% 0.21/0.58    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl5_28),
% 0.21/0.58    inference(resolution,[],[f364,f40])).
% 0.21/0.58  fof(f364,plain,(
% 0.21/0.58    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl5_28),
% 0.21/0.58    inference(avatar_component_clause,[],[f362])).
% 0.21/0.58  fof(f362,plain,(
% 0.21/0.58    spl5_28 <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.58  fof(f365,plain,(
% 0.21/0.58    spl5_28 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_14 | ~spl5_16 | ~spl5_18 | ~spl5_25),
% 0.21/0.58    inference(avatar_split_clause,[],[f339,f300,f207,f187,f165,f117,f70,f65,f60,f55,f50,f362])).
% 0.21/0.58  fof(f117,plain,(
% 0.21/0.58    spl5_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    spl5_14 <=> k1_xboole_0 = sK1),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.58  fof(f207,plain,(
% 0.21/0.58    spl5_18 <=> r2_hidden(sK4(sK2,k1_xboole_0),sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.58  fof(f339,plain,(
% 0.21/0.58    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_14 | ~spl5_16 | ~spl5_18 | ~spl5_25)),
% 0.21/0.58    inference(backward_demodulation,[],[f209,f331])).
% 0.21/0.58  fof(f331,plain,(
% 0.21/0.58    k1_xboole_0 = sK2 | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_14 | ~spl5_16 | ~spl5_25)),
% 0.21/0.58    inference(resolution,[],[f320,f189])).
% 0.21/0.58  fof(f320,plain,(
% 0.21/0.58    ( ! [X2] : (~m1_orders_2(X2,sK0,k1_xboole_0) | k1_xboole_0 = X2) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_14 | ~spl5_25)),
% 0.21/0.58    inference(subsumption_resolution,[],[f319,f287])).
% 0.21/0.58  fof(f287,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_orders_2(X0,sK0,k1_xboole_0) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_14)),
% 0.21/0.58    inference(backward_demodulation,[],[f136,f167])).
% 0.21/0.58  fof(f167,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | ~spl5_14),
% 0.21/0.58    inference(avatar_component_clause,[],[f165])).
% 0.21/0.58  fof(f136,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8)),
% 0.21/0.58    inference(resolution,[],[f83,f119])).
% 0.21/0.58  fof(f119,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_8),
% 0.21/0.58    inference(avatar_component_clause,[],[f117])).
% 0.21/0.58  fof(f209,plain,(
% 0.21/0.58    r2_hidden(sK4(sK2,k1_xboole_0),sK2) | ~spl5_18),
% 0.21/0.58    inference(avatar_component_clause,[],[f207])).
% 0.21/0.58  fof(f303,plain,(
% 0.21/0.58    spl5_25 | ~spl5_8 | ~spl5_14),
% 0.21/0.58    inference(avatar_split_clause,[],[f171,f165,f117,f300])).
% 0.21/0.58  fof(f171,plain,(
% 0.21/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_8 | ~spl5_14)),
% 0.21/0.58    inference(backward_demodulation,[],[f119,f167])).
% 0.21/0.58  fof(f263,plain,(
% 0.21/0.58    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_11 | spl5_14 | spl5_21),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f262])).
% 0.21/0.58  fof(f262,plain,(
% 0.21/0.58    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_11 | spl5_14 | spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f261,f114])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    m1_orders_2(sK2,sK0,sK1) | ~spl5_7),
% 0.21/0.58    inference(avatar_component_clause,[],[f112])).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    spl5_7 <=> m1_orders_2(sK2,sK0,sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.58  fof(f261,plain,(
% 0.21/0.58    ~m1_orders_2(sK2,sK0,sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_11 | spl5_14 | spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f260,f52])).
% 0.21/0.58  fof(f260,plain,(
% 0.21/0.58    v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_11 | spl5_14 | spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f259,f166])).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    k1_xboole_0 != sK1 | spl5_14),
% 0.21/0.58    inference(avatar_component_clause,[],[f165])).
% 0.21/0.58  fof(f259,plain,(
% 0.21/0.58    k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_11 | spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f258,f141])).
% 0.21/0.58  fof(f258,plain,(
% 0.21/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f257,f119])).
% 0.21/0.58  fof(f257,plain,(
% 0.21/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f256,f72])).
% 0.21/0.58  fof(f256,plain,(
% 0.21/0.58    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f255,f67])).
% 0.21/0.58  fof(f255,plain,(
% 0.21/0.58    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1) | (~spl5_2 | ~spl5_3 | spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f254,f62])).
% 0.21/0.58  fof(f254,plain,(
% 0.21/0.58    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1) | (~spl5_2 | spl5_21)),
% 0.21/0.58    inference(subsumption_resolution,[],[f251,f57])).
% 0.21/0.58  fof(f251,plain,(
% 0.21/0.58    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | v2_struct_0(sK0) | ~m1_orders_2(sK2,sK0,sK1) | spl5_21),
% 0.21/0.58    inference(resolution,[],[f246,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | v2_struct_0(X0) | ~m1_orders_2(X2,X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f14])).
% 0.21/0.58  fof(f246,plain,(
% 0.21/0.58    ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl5_21),
% 0.21/0.58    inference(avatar_component_clause,[],[f244])).
% 0.21/0.58  fof(f244,plain,(
% 0.21/0.58    spl5_21 <=> m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.58  fof(f250,plain,(
% 0.21/0.58    ~spl5_21 | spl5_22 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_13),
% 0.21/0.58    inference(avatar_split_clause,[],[f232,f161,f117,f70,f65,f60,f55,f50,f248,f244])).
% 0.21/0.58  fof(f161,plain,(
% 0.21/0.58    spl5_13 <=> sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.58  fof(f232,plain,(
% 0.21/0.58    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_13)),
% 0.21/0.58    inference(subsumption_resolution,[],[f229,f119])).
% 0.21/0.59  % (19054)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.60  % (19046)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.60  fof(f229,plain,(
% 0.21/0.60    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_13)),
% 0.21/0.60    inference(superposition,[],[f99,f163])).
% 0.21/0.60  fof(f163,plain,(
% 0.21/0.60    sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | ~spl5_13),
% 0.21/0.60    inference(avatar_component_clause,[],[f161])).
% 0.21/0.60  fof(f99,plain,(
% 0.21/0.60    ( ! [X10,X11,X9] : (~r2_hidden(X9,k3_orders_2(sK0,X11,X10)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~m1_subset_1(X9,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.60    inference(subsumption_resolution,[],[f98,f52])).
% 0.21/0.60  fof(f98,plain,(
% 0.21/0.60    ( ! [X10,X11,X9] : (v2_struct_0(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~r2_hidden(X9,k3_orders_2(sK0,X11,X10))) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.60    inference(subsumption_resolution,[],[f97,f67])).
% 0.21/0.60  fof(f97,plain,(
% 0.21/0.60    ( ! [X10,X11,X9] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~r2_hidden(X9,k3_orders_2(sK0,X11,X10))) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.60    inference(subsumption_resolution,[],[f96,f62])).
% 0.21/0.60  fof(f96,plain,(
% 0.21/0.60    ( ! [X10,X11,X9] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~r2_hidden(X9,k3_orders_2(sK0,X11,X10))) ) | (~spl5_2 | ~spl5_5)),
% 0.21/0.60    inference(subsumption_resolution,[],[f78,f57])).
% 0.21/0.60  fof(f78,plain,(
% 0.21/0.60    ( ! [X10,X11,X9] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,X11) | ~r2_hidden(X9,k3_orders_2(sK0,X11,X10))) ) | ~spl5_5),
% 0.21/0.60    inference(resolution,[],[f72,f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f11])).
% 0.21/0.60  fof(f11,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.60  fof(f210,plain,(
% 0.21/0.60    spl5_18 | spl5_15),
% 0.21/0.60    inference(avatar_split_clause,[],[f185,f181,f207])).
% 0.21/0.60  fof(f185,plain,(
% 0.21/0.60    r2_hidden(sK4(sK2,k1_xboole_0),sK2) | spl5_15),
% 0.21/0.60    inference(resolution,[],[f183,f39])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f17])).
% 0.21/0.60  fof(f190,plain,(
% 0.21/0.60    spl5_16 | ~spl5_7 | ~spl5_14),
% 0.21/0.60    inference(avatar_split_clause,[],[f170,f165,f112,f187])).
% 0.21/0.60  fof(f170,plain,(
% 0.21/0.60    m1_orders_2(sK2,sK0,k1_xboole_0) | (~spl5_7 | ~spl5_14)),
% 0.21/0.60    inference(backward_demodulation,[],[f114,f167])).
% 0.21/0.60  fof(f184,plain,(
% 0.21/0.60    ~spl5_15 | spl5_6 | ~spl5_14),
% 0.21/0.60    inference(avatar_split_clause,[],[f169,f165,f106,f181])).
% 0.21/0.60  fof(f169,plain,(
% 0.21/0.60    ~r1_tarski(sK2,k1_xboole_0) | (spl5_6 | ~spl5_14)),
% 0.21/0.60    inference(backward_demodulation,[],[f108,f167])).
% 0.21/0.60  fof(f168,plain,(
% 0.21/0.60    spl5_13 | spl5_14 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_11),
% 0.21/0.60    inference(avatar_split_clause,[],[f157,f139,f117,f112,f70,f65,f60,f55,f50,f165,f161])).
% 0.21/0.60  fof(f157,plain,(
% 0.21/0.60    k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_11)),
% 0.21/0.60    inference(subsumption_resolution,[],[f156,f119])).
% 0.21/0.61  fof(f156,plain,(
% 0.21/0.61    k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_11)),
% 0.21/0.61    inference(subsumption_resolution,[],[f155,f141])).
% 0.21/0.61  fof(f155,plain,(
% 0.21/0.61    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7)),
% 0.21/0.61    inference(resolution,[],[f91,f114])).
% 0.21/0.61  fof(f91,plain,(
% 0.21/0.61    ( ! [X4,X5] : (~m1_orders_2(X5,sK0,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.61    inference(subsumption_resolution,[],[f90,f52])).
% 0.21/0.61  fof(f90,plain,(
% 0.21/0.61    ( ! [X4,X5] : (v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_orders_2(X5,sK0,X4)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.21/0.61    inference(subsumption_resolution,[],[f89,f67])).
% 0.21/0.61  fof(f89,plain,(
% 0.21/0.61    ( ! [X4,X5] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_orders_2(X5,sK0,X4)) ) | (~spl5_2 | ~spl5_3 | ~spl5_5)),
% 0.21/0.61    inference(subsumption_resolution,[],[f88,f62])).
% 0.21/0.61  fof(f88,plain,(
% 0.21/0.61    ( ! [X4,X5] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_orders_2(X5,sK0,X4)) ) | (~spl5_2 | ~spl5_5)),
% 0.21/0.61    inference(subsumption_resolution,[],[f76,f57])).
% 0.21/0.61  fof(f76,plain,(
% 0.21/0.61    ( ! [X4,X5] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X4 | k3_orders_2(sK0,X4,sK3(sK0,X4,X5)) = X5 | ~m1_orders_2(X5,sK0,X4)) ) | ~spl5_5),
% 0.21/0.61    inference(resolution,[],[f72,f33])).
% 0.21/0.61  fof(f33,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f14])).
% 0.21/0.61  fof(f142,plain,(
% 0.21/0.61    spl5_11 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8),
% 0.21/0.61    inference(avatar_split_clause,[],[f137,f117,f112,f70,f65,f60,f55,f50,f139])).
% 0.21/0.61  fof(f137,plain,(
% 0.21/0.61    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8)),
% 0.21/0.61    inference(resolution,[],[f136,f114])).
% 0.21/0.61  fof(f133,plain,(
% 0.21/0.61    spl5_10 | spl5_6),
% 0.21/0.61    inference(avatar_split_clause,[],[f110,f106,f130])).
% 0.21/0.61  fof(f110,plain,(
% 0.21/0.61    r2_hidden(sK4(sK2,sK1),sK2) | spl5_6),
% 0.21/0.61    inference(resolution,[],[f108,f39])).
% 0.21/0.61  fof(f120,plain,(
% 0.21/0.61    spl5_8),
% 0.21/0.61    inference(avatar_split_clause,[],[f22,f117])).
% 0.21/0.61  fof(f22,plain,(
% 0.21/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.61    inference(cnf_transformation,[],[f10])).
% 0.21/0.61  fof(f10,plain,(
% 0.21/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.61    inference(flattening,[],[f9])).
% 0.21/0.61  fof(f9,plain,(
% 0.21/0.61    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.61    inference(ennf_transformation,[],[f8])).
% 0.21/0.61  fof(f8,negated_conjecture,(
% 0.21/0.61    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.61    inference(negated_conjecture,[],[f7])).
% 0.21/0.61  fof(f7,conjecture,(
% 0.21/0.61    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.21/0.61  fof(f115,plain,(
% 0.21/0.61    spl5_7),
% 0.21/0.61    inference(avatar_split_clause,[],[f20,f112])).
% 0.21/0.61  fof(f20,plain,(
% 0.21/0.61    m1_orders_2(sK2,sK0,sK1)),
% 0.21/0.61    inference(cnf_transformation,[],[f10])).
% 0.21/0.61  fof(f109,plain,(
% 0.21/0.61    ~spl5_6),
% 0.21/0.61    inference(avatar_split_clause,[],[f21,f106])).
% 0.21/0.61  fof(f21,plain,(
% 0.21/0.61    ~r1_tarski(sK2,sK1)),
% 0.21/0.61    inference(cnf_transformation,[],[f10])).
% 0.21/0.61  fof(f73,plain,(
% 0.21/0.61    spl5_5),
% 0.21/0.61    inference(avatar_split_clause,[],[f27,f70])).
% 0.21/0.61  fof(f27,plain,(
% 0.21/0.61    l1_orders_2(sK0)),
% 0.21/0.61    inference(cnf_transformation,[],[f10])).
% 0.21/0.61  fof(f68,plain,(
% 0.21/0.61    spl5_4),
% 0.21/0.61    inference(avatar_split_clause,[],[f26,f65])).
% 0.21/0.61  fof(f26,plain,(
% 0.21/0.61    v5_orders_2(sK0)),
% 0.21/0.61    inference(cnf_transformation,[],[f10])).
% 0.21/0.61  fof(f63,plain,(
% 0.21/0.61    spl5_3),
% 0.21/0.61    inference(avatar_split_clause,[],[f25,f60])).
% 0.21/0.61  fof(f25,plain,(
% 0.21/0.61    v4_orders_2(sK0)),
% 0.21/0.61    inference(cnf_transformation,[],[f10])).
% 0.21/0.61  fof(f58,plain,(
% 0.21/0.61    spl5_2),
% 0.21/0.61    inference(avatar_split_clause,[],[f24,f55])).
% 0.21/0.61  fof(f24,plain,(
% 0.21/0.61    v3_orders_2(sK0)),
% 0.21/0.61    inference(cnf_transformation,[],[f10])).
% 0.21/0.61  fof(f53,plain,(
% 0.21/0.61    ~spl5_1),
% 0.21/0.61    inference(avatar_split_clause,[],[f23,f50])).
% 0.21/0.61  fof(f23,plain,(
% 0.21/0.61    ~v2_struct_0(sK0)),
% 0.21/0.61    inference(cnf_transformation,[],[f10])).
% 0.21/0.61  % SZS output end Proof for theBenchmark
% 0.21/0.61  % (19055)------------------------------
% 0.21/0.61  % (19055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (19055)Termination reason: Refutation
% 0.21/0.61  
% 0.21/0.61  % (19055)Memory used [KB]: 11129
% 0.21/0.61  % (19055)Time elapsed: 0.175 s
% 0.21/0.61  % (19055)------------------------------
% 0.21/0.61  % (19055)------------------------------
% 0.21/0.61  % (19034)Success in time 0.24 s
%------------------------------------------------------------------------------
